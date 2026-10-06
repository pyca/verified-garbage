import VerifiedGarbage.Proof.Rsa.AArch64.PrivArgs

/-!
# `vg_rsa_private_checked` on AArch64: calls from the frames

`call_ok` runs a call of verified code without frames from a state in which
`Ctx` and `Slots` hold, given regions within ours to read and, to write,
regions within `out`, `scratch` or the inner frame above the slots: they
hold again afterwards.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region :=
  [L.N, L.E, L.IN, L.P, L.Q, L.DP, L.DQ, L.QI, L.ARGS, L.FR, L.OUT, L.SC]

/-- The inner frame above the slots: `M` and `n`'s values. -/
abbrev Lay.HI (L : Lay) : Region := ⟨L.B + BitVec.ofNat 64 oM, frameBytes - oM⟩

/-- A region a callee may write. -/
def InW (L : Lay) (r : Region) : Prop := Within r L.OUT ∨ Within r L.SC ∨ Within r L.HI

theorem InW.sub {L : Lay} (hL : L.Ok) {r : Region} (h : InW L r) :
    ∃ R ∈ [L.OUT, L.SC, L.STK], Region.Sub r R := by
  have hnB := hL.nB
  rcases h with h | h | h
  · exact ⟨_, by simp, h.sub⟩
  · exact ⟨_, by simp, h.sub⟩
  · refine ⟨L.STK, by simp, fun a ha => ?_⟩
    exact Offset.sub_base L.B (d := oM) (n := frameBytes - oM) (k := stackBytes) (by decide) a (h.sub a ha)

/-- A region a callee may write misses the slots and our return address. -/
theorem InW.disj {L : Lay} (hL : L.Ok) {r : Region} (h : InW L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ r ∧ Region.Disjoint L.LR r := by
  have hnB := hL.nB
  rcases h with h | h | h
  · have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ L.STK :=
      Offset.sub_base _ (by decide)
    have hs' : Region.Sub L.LR L.STK := Offset.sub_base _ (by decide)
    exact ⟨(hL.ko.sub_left hs).sub_right h.sub, (hL.ko.sub_left hs').sub_right h.sub⟩
  · have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ L.STK :=
      Offset.sub_base _ (by decide)
    have hs' : Region.Sub L.LR L.STK := Offset.sub_base _ (by decide)
    exact ⟨(hL.ksc.sub_left hs).sub_right h.sub, (hL.ksc.sub_left hs').sub_right h.sub⟩
  · exact ⟨(Offset.disjoint L.B (d := oOut) (n := 48) (e := oM) (k := frameBytes - oM) (by decide)
        (by simp only [oOut]; omega) (by simp only [oM, frameBytes]; omega)).sub_right h.sub,
      (Offset.disjoint L.B (d := frameBytes) (n := 16) (e := oM) (k := frameBytes - oM) (by decide)
        (by simp only [frameBytes]; omega) (by simp only [oM, frameBytes]; omega)).sub_right h.sub⟩

theorem covers {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InW L r) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr]
    rcases hwsub r hr with h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · obtain ⟨off, hb, hl⟩ := h
      refine ⟨L.FR, by simp, oM + off, ?_, ?_⟩
      · rw [hb, add_add]
      · simp only [oM, frameBytes] at hl ⊢; omega

/-- A call of verified code without frames, given regions within ours to
read, and within `out`, `scratch` or the inner frame above the slots to
write: afterwards `Ctx` and `Slots` hold again, memory changed only within
what it writes, and the callee's postcondition holds. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InW L r)
    {Q : State → Prop}
    (hQ : ∀ s', Ctx L g vv m₀ s' → Slots L s'.mem → Frame wr t.mem s'.mem →
      k.post (t.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨hcov, hcovw⟩ := covers hc hsub hwsub
  refine WP.callV hv hpre hcov hcovw (fun s' hrd hwr hsp hf hcs _ hvs hpost => ?_) hn
  have hnB := hL.nB
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'), fun r hr => (hvs r hr).trans (hc.vs r hr),
    ?_, hc.frame.trans (Frame.sub hf fun r hr => (hwsub r hr).sub hL)⟩
    (hs.frame hf (fun R hR => ((hwsub R hR).disj hL).1) (by omega)) hf hpost
  have hlr : L.LR.Contains (L.B + BitVec.ofNat 64 frameBytes) (64 / 8) := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  rw [hf.readW hlr (fun R hR => ((hwsub R hR).disj hL).2) (by decide)]
  exact hc.lr

end VG.Proof.Rsa.AArch64
