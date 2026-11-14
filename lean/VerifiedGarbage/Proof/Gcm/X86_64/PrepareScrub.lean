module

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
meta import VerifiedGarbage.Spec.Gcm.Prepared
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
meta import VerifiedGarbage.Proof.Gcm.X86_64.PrepareZ
meta import VerifiedGarbage.Proof.Gcm.X86_64.Prepare16
meta import VerifiedGarbage.Proof.Gcm.X86_64.PrepareAvx.Ok
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Preparing AES-GCM's key context on x86-64, without secret residue

Each implementation of `vg_aes_gcm_prepare`, followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers that the residue analysis (`X86_64.RTaint`) finds may hold
secrets. Its postcondition reads the memory on return only within the
context (`prepareOut`). `vg_aes_gcm_wipe_prepared` branches on the count of
powers, which its contract leaks only as `flagLeak`, while the analysis needs
the count's bytes public: it has no stack, and only its registers are
cleared (`X86_64.Scrub.withScrubAll`, `wipeReg`).
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

def zKs : List Nat := keep_for% Spec.Gcm.prepareApi.sig 0 (Impl.Gcm.X86_64.Flag.prepareFlagged 48 Impl.Gcm.X86_64.PrepareZ.prepare) []

theorem zOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Gcm.prepareApi.sig 0 [])
      (Impl.Gcm.X86_64.Flag.prepareFlagged 48 Impl.Gcm.X86_64.PrepareZ.prepare) h).any
      (RScrub.resOkB · 0 zKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of zKs (by taint_decide)

def p16Ks : List Nat := keep_for% Spec.Gcm.prepareApi.sig 0 (Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.Prepare16.prepare16) []

theorem p16Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Gcm.prepareApi.sig 0 [])
      (Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.Prepare16.prepare16) h).any
      (RScrub.resOkB · 0 p16Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of p16Ks (by taint_decide)

def avxKs : List Nat := keep_for% Spec.Gcm.prepareApi.sig 0 (Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.PrepareAvx.prepare16) []

theorem avxOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Gcm.prepareApi.sig 0 [])
      (Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.PrepareAvx.prepare16) h).any
      (RScrub.resOkB · 0 avxKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of avxKs (by taint_decide)

def absentKs : List Nat := keep_for% Spec.Gcm.prepareApi.sig 0 Impl.Gcm.X86_64.Flag.prepareAbsent []

theorem absentOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Gcm.prepareApi.sig 0 [])
      Impl.Gcm.X86_64.Flag.prepareAbsent h).any
      (RScrub.resOkB · 0 absentKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of absentKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_aes_gcm_prepare_vpclmul_avx512`. -/
def zReg : Registration Spec.Gcm.prepareApi X86_64.target :=
  withScrub {
    suffix := "_vpclmul_avx512"
    code := Impl.Gcm.X86_64.Flag.prepareFlagged 48 Impl.Gcm.X86_64.PrepareZ.prepare
    verified := Proof.Gcm.X86_64.PrepareZ.prepareFlagged_verified }
    (prepareOut _) [] (pubOk_nil _) (some ⟨zKs, zOk⟩)

open VG.X86_64.RScrub in
/-- `vg_aes_gcm_prepare_vpclmul`. -/
def p16Reg : Registration Spec.Gcm.prepareApi X86_64.target :=
  withScrub {
    suffix := "_vpclmul"
    code := Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.Prepare16.prepare16
    verified := Proof.Gcm.X86_64.Prepare16.prepareFlagged_verified }
    (prepareOut _) [] (pubOk_nil _) (some ⟨p16Ks, p16Ok⟩)

open VG.X86_64.RScrub in
/-- `vg_aes_gcm_prepare_pclmul_avx`. -/
def avxReg : Registration Spec.Gcm.prepareApi X86_64.target :=
  withScrub {
    suffix := "_pclmul_avx"
    code := Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.PrepareAvx.prepare16
    verified := Proof.Gcm.X86_64.PrepareAvx.prepareFlagged_verified }
    (prepareOut _) [] (pubOk_nil _) (some ⟨avxKs, avxOk⟩)

open VG.X86_64.RScrub in
/-- `vg_aes_gcm_prepare`. -/
def absentReg : Registration Spec.Gcm.prepareApi X86_64.target :=
  withScrub {
    suffix := ""
    code := Impl.Gcm.X86_64.Flag.prepareAbsent
    verified := Proof.Gcm.X86_64.Prepare.absent_verified }
    (prepareOut _) [] (pubOk_nil _) (some ⟨absentKs, absentOk⟩)

/-- `vg_aes_gcm_wipe_prepared`, with AVX if `avx`, with its registers
cleared (`withScrubAll`; it has no stack): it branches on the count of
powers, which its contract leaks only as `flagLeak`, while the residue
analysis needs the count's bytes public. -/
def wipeReg (avx : Bool) : Registration Spec.Gcm.wipePreparedApi X86_64.target :=
  withScrubAll {
    suffix := if avx then "_avx" else ""
    code := Impl.Gcm.X86_64.Flag.wipe avx
    verified := Proof.Gcm.X86_64.Prepare.wipe_verified avx }
    (wipePreparedOut _)

end VG.Proof.Gcm.X86_64.PrepareScrub
