module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSOps
public import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Dsa.Arm.Gen.CT
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP

/-! # DSA parameter generation on ARMv7: the division

`divHdr_vp`: the division's header; `div_vp`: the division
(`Impl/Rsa/Arm/Div.lean`, `Proof/Rsa/Arm/KeyDiv.lean`), which changes `r7`
and `r9` (`SS79`: a state of the search once they are set back); `wRegs_vp`:
`r9` and `r7` set back. The division's constant time is proven on the state
narrowed to the key working space (`RelCT.narrow`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr stride)
open VG.Impl.Rsa.Arm.CrtValues (divHdr)
open VG.Proof.X25519.Arm (Rest Upd wp_mov op2_imm)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- Two runs of `c` leak the same trace if its runs from the states narrowed
to the regions `rd`, `wr` do, and exist (as `Proof/MlDsa/Arm/Pack/HintCT.lean`). -/
theorem RelCT.narrow {c : Prog isa} {P : State → State → Prop} (rd wr : State → List Region)
    (hc : ∀ a b, P a b → Covers (rd a ++ wr a) (a.rd ++ a.wr) ∧ Covers (wr a) a.wr ∧
      Covers (rd b ++ wr b) (b.rd ++ b.wr) ∧ Covers (wr b) b.wr)
    (hrun : ∀ a b, P a b → (∃ t s', Exec isa c (a.withRegions (rd a) (wr a)) t s') ∧
      ∃ t s', Exec isa c (b.withRegions (rd b) (wr b)) t s')
    (hct : RelCT isa (fun a' b' => ∃ a b, P a b ∧ a' = a.withRegions (rd a) (wr a) ∧
      b' = b.withRegions (rd b) (wr b)) c fun _ _ => True) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨c₁, w₁, c₂, w₂⟩ := hc _ _ hp
  obtain ⟨⟨u₁, n₁, f₁⟩, ⟨u₂, n₂, f₂⟩⟩ := hrun _ _ hp
  have g₁ := Exec.widen f₁ (rd := s₁.rd) (wr := s₁.wr) (by simpa using c₁) (by simpa using w₁)
  have g₂ := Exec.widen f₂ (rd := s₂.rd) (wr := s₂.wr) (by simpa using c₂) (by simpa using w₂)
  simp only [State.withRegions_withRegions, State.withRegions_self] at g₁ g₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ g₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ g₂
  exact ⟨(hct _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ f₁ f₂).1, trivial⟩

/-- Every register. -/
abbrev allRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- A state of the search once `r7` and `r9` are set back. -/
def SS79 (G : GP) (σ : State) (c : Cfg) (t : State) : Prop :=
  ∀ t' : State, t'.mem = t.mem → t'.sp = t.sp → t'.rd = t.rd → t'.wr = t.wr → t'.gpr .r8 = t.gpr .r8 →
    t'.gpr .r7 = BitVec.ofNat 32 (S G.w) → t'.gpr .r9 = BitVec.ofNat 32 G.w → SS G σ c t'

/-- The top word of array `d`. -/
abbrev Top (G : GP) (m : Mem) (d : Nat) : Prop := w32 m (State.addr G.KB) (arr G.w d + 4 * G.w) = 0

/-- `r9` and `r7` set back. -/
theorem wRegs_vp {L : Nat} (hL : L = G.pLen) (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    VP (fun σ t => SS79 G σ c t ∧ X σ) (.block (wRegs L)) (St G c X) := by
  refine VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs []) (.block (wRegs 128)), rfl⟩
    (fun _ _ _ _ _ _ r hr => absurd hr (by simp)) fun σ s ⟨h, x⟩ => ?_
  subst hL
  have w96 : G.pLen / 4 < 256 := by omega
  refine wp_mov (op2_imm (encodable_lt w96)) fun s₁ u₁ => ?_
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (w := G.w) (by simp only [GP.w]; omega) u₁.gpr fun t e7 R m => ?_
  refine WP.block_nil ⟨h t (m.trans u₁.mem) (R.sp.trans u₁.sp) (R.rd.trans u₁.rd) (R.wr.trans u₁.wr)
    (by rw [R.gpr _ (by decide), u₁.other _ (by decide)]) e7 (by rw [R.gpr _ (by decide), u₁.gpr]), x⟩

/-- The division's header: the arrays `q`, `r`, `d` and `t`, with the
count already at word 16. -/
theorem divHdr_vp {q r d t : Nat} (cert : Cert7 (.block (divHdr q r d t))) (hq : q < 256) (hr : r < 256)
    (hd : d < nArrs) (ht : t < 256) (h16 : 16 ∈ c.kls) (hv16 : c.KV 16 = G.w) (hkls : ∀ e ∈ c.kls, 16 ≤ e) :
    VP (fun σ s => St G c X σ s ∧ Top G s.mem d) (.block (divHdr q r d t))
      (fun σ s => St G c X σ s ∧ Top G s.mem d ∧ DivHdr s.mem G.KB G.w q r d t) := by
  refine ks_vp cert (fun σ s h => h.1.1) fun σ s ⟨⟨h, x⟩, top⟩ => ?_
  have hw := h.ws
  have cnt : s.mem.readW (off (State.addr G.KB) 16) 32 = BitVec.ofNat 32 G.w := by
    have e := h.ksl 16 h16
    rw [hv16] at e
    apply BitVec.eq_of_toNat_eq
    rw [← show slot s.mem G.KB 16 = (s.mem.readW (off (State.addr G.KB) 16) 32).toNat from rfl, e,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hw.wle; omega)]
  refine h.ksOp (js := []) (ds := [0, 4, 8, 12]) (P := fun u => DivHdr u.mem G.KB G.w q r d t) rfl
    (by rw [← List.append_nil (divHdr q r d t)]
        exact VG.Proof.Rsa.Arm.CrtValues.divHdr_ok hw hq hr (by simp only [nArrs] at hd; omega) ht cnt fun u w k v R => WP.block_nil ⟨w, k, v, R⟩)
    fun u k v R f => ⟨⟨?_, x⟩, ?_, v⟩
  · have sl : ∀ e ∈ c.kls, slot u.mem G.KB e = c.KV e := fun e he => by
      have h16' := hkls e he
      have ap : ∀ d' ∈ [0, 4, 8, 12], e + 4 ≤ d' ∨ d' + 4 ≤ e := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro d' (rfl | rfl | rfl | rfl) <;> omega
      rw [k.slot (h.kslOk e he).1 ap]
      exact h.ksl e he
    exact h.of_ks R f (h.arrs.keep k hw (fun j hj => ⟨h.liveOk j hj, by simp⟩) (by simp [hdr])) h.liveOk sl
      h.kslOk
  · have := hw.wle
    show w32 u.mem _ _ = 0
    rw [show arr G.w d + 4 * G.w = arr G.w d + 4 * G.w from rfl,
      k.word (j := d) (i := G.w) (by simp only [S]; omega) (by simp) (by simp [hdr]) (hw.fit64 hd)]
    exact top

/-- The stage after the division. -/
abbrev divCfg (c : Cfg) (q r d : Nat) : Cfg :=
  { c with A := KU (KU c.A q (c.A q / c.A d)) r (c.A q % c.A d), live := q :: r :: c.live }

/-- The division: `[q] := [q] / [d]`, `[r] := [q] mod [d]`, the temporary `t`
lost, and `r7` and `r9` changed. -/
theorem div_vp {q r d t : Nat} (hq : q < nArrs) (hr : r < nArrs) (hd : d < nArrs) (ht : t < nArrs)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hqL : q ∈ c.live) (hdL : d ∈ c.live) (htL : t ∉ c.live) (hpos : 0 < c.A d) :
    VP (fun σ s => St G c X σ s ∧ Top G s.mem d ∧ DivHdr s.mem G.KB G.w q r d t) VG.Impl.Rsa.Arm.Div.code
      (fun σ s => SS79 G σ (divCfg c q r d) s ∧ X σ) := by
  have run : ∀ σ s, St G c X σ s → Top G s.mem d → DivHdr s.mem G.KB G.w q r d t →
      WP isa VG.Impl.Rsa.Arm.Div.code (G.ksState s) fun u => Keep G.KB G.w [q, r, t] [] s.mem u.mem ∧
        Rest (.r6 :: VG.Proof.Rsa.Arm.Div.clobbers) (G.ksState s) u ∧
        (0 < num s.mem G.KB G.w d → num u.mem G.KB G.w r = num s.mem G.KB G.w q % num s.mem G.KB G.w d ∧
          num u.mem G.KB G.w q = num s.mem G.KB G.w q / num s.mem G.KB G.w d) :=
    fun σ s ⟨h, _⟩ top hh => div_ok h.ws hq hr hd ht hqr hqd hqt hrd hrt hdt hh top
  refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨h, x⟩, top, hh⟩ => ?_
  · refine RelCT.narrow (fun a => a.rd) (fun _ => [G.rK]) (fun a b ⟨⟨⟨ha, _⟩, _⟩, ⟨⟨hb, _⟩, _⟩⟩ =>
      ⟨ha.kcov.1, ha.kcov.2, hb.kcov.1, hb.kcov.2⟩) (fun a b ⟨⟨ha, ta, da⟩, ⟨hb, tb, db⟩⟩ =>
      ⟨let ⟨t, s', e, _⟩ := run _ _ ha ta da; ⟨t, s', e⟩, let ⟨t, s', e, _⟩ := run _ _ hb tb db; ⟨t, s', e⟩⟩) ?_
    refine (VG.Proof.Rsa.Arm.Div.code_ct (g := divGeom G.KB (kz G.pLen) G.w q r d t)).mono
      (fun a' b' ⟨a, b, ⟨⟨⟨ha, _⟩, _, da⟩, ⟨⟨hb, _⟩, _, db⟩⟩, ea, eb⟩ => ?_) fun _ _ _ => trivial
    subst ea eb
    exact ⟨divGeom_ctx ha.ws hq hr hd ht hqr hqd hqt hrd hrt hdt da,
      divGeom_ctx hb.ws hq hr hd ht hqr hqd hqt hrd hrt hdt db⟩
  refine h.ksWP rfl (run σ s ⟨h, x⟩ top hh) fun u ⟨k, R, v⟩ hr' hw' f => ⟨fun t' m sp rd wr e8 e7 e9 => ?_, x⟩
  have hw := h.ws
  have va := h.arrs.get hqL
  have vd := h.arrs.get hdL
  obtain ⟨vr, vq⟩ := v (by rw [vd]; exact hpos)
  simp only [GP.ksState, State.withRegions_mem] at vr vq k
  rw [va, vd] at vr vq
  have R' : Rest allRegs s t' := ⟨fun r hr => absurd (mem_allRegs r) hr, rd.trans hr', wr.trans hw',
    sp.trans (R.sp)⟩
  have e8' : t'.gpr .r8 = G.KB := by
    rw [e8]; exact (R.gpr .r8 (by decide)).trans h.r8
  refine h.of_ks' R' (m ▸ f) (fun j hj => ?_) (fun j hj => ?_) (fun e he => ?_) h.kslOk e7 e8' e9
  · rw [m]
    simp only [List.mem_cons] at hj
    show num u.mem G.KB G.w j = KU (KU c.A q (c.A q / c.A d)) r (c.A q % c.A d) j
    simp only [KU]
    by_cases ejr : j = r
    · subst ejr; rw [VG.Proof.Rsa.Arm.Keys.upd_self]; exact vr
    rw [VG.Proof.Rsa.Arm.Keys.upd_ne _ _ ejr]
    by_cases ejq : j = q
    · subst ejq; rw [VG.Proof.Rsa.Arm.Keys.upd_self]; exact vq
    rw [VG.Proof.Rsa.Arm.Keys.upd_ne _ _ ejq]
    have jl : j ∈ c.live := by rcases hj with rfl | rfl | hj <;> first | exact absurd rfl ejq | exact absurd rfl ejr | exact hj
    have ejt : j ≠ t := fun e => htL (e ▸ jl)
    rw [k.num (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro k' (rfl | rfl | rfl) <;> omega)
      (by simp) (hw.fit64 (h.liveOk j jl))]
    exact h.arrs.get jl
  · simp only [List.mem_cons] at hj
    rcases hj with rfl | rfl | hj
    · exact hq
    · exact hr
    · exact h.liveOk j hj
  · rw [m, k.slot (h.kslOk e he).1 (by simp)]; exact h.ksl e he

end

end VG.Proof.Dsa.Arm.Gen
