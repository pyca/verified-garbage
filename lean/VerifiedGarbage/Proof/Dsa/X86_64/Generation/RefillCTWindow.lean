module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Refill
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorPlanCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Refill
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillOutcome
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorPlanCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Timing of the refillable-tape search's `h` window

Before its generator search, a seed of the refillable-tape search points
its `h` tape (frame words 11 and 12) at the window of the witness tape after
its witnesses (`Refill.window`). The window's start and length are public:
the witness tape's octets consumed and its length. `SeedGeneratorPublic.windowed`
is the generator search's public input over that window. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Mgf1.X86_64 (sp)

/-- The window's length from the witness tape's `u`-th octet. -/
def GenerationContext.ctWindowLen (c : GenerationContext) (u : Nat) : Nat :=
  min (c.rand.bytes.length - u) (Impl.Dsa.X86_64.Generation.Refill.windowBytes c.geo.pLen)

theorem GenerationContext.ctWindow_fit (c : GenerationContext) {u : Nat} (hu : u ≤ c.rand.bytes.length) :
    u + c.ctWindowLen u ≤ c.rand.bytes.length := by
  unfold ctWindowLen; omega

/-- The window from the witness tape's `u`-th octet. -/
def GenerationContext.ctWindow (c : GenerationContext) (u : Nat) (hu : u ≤ c.rand.bytes.length) :
    GenerationTape c.geo :=
  c.rand.window u (c.ctWindowLen u) (c.ctWindow_fit hu)

/-- The generator search's public input over the window after the seed's witnesses. -/
def SeedGeneratorPublic.windowed (g : SeedGeneratorPublic) : SeedGeneratorPublic where
  seed :=
    { context := g.seed.context.withHs (g.seed.context.ctWindow g.seed.used g.seed.bound)
      seed := g.seed.seed
      length := g.seed.length
      used := g.seed.used
      seedCursor := g.seed.seedCursor
      bound := g.seed.bound
      ws := g.seed.ws
      wr := g.seed.wr
      header := g.seed.header }
  value := g.value
  domain := g.domain

theorem ctFrame_bytes {g : GenerationGeometry} {m m' : Mem}
    (hf : Frame [⟨g.F, frameBytes⟩] m m') {d n : Nat} (hd : d + n ≤ usedBytes g.pLen) :
    Spec.Rsa.bytesAt m' (off g.B d) n = Spec.Rsa.bytesAt m (off g.B d) n := by
  have pn : g.pLen ≤ 384 := by rcases g.width with hh | hh | hh <;> omega
  apply VG.Proof.Dsa.Generation.frame_bytesAt hf
  · intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact (g.frame_part hd).symm
  · unfold usedBytes domainCheck at hd; omega

/-- Two word stores to the frame change only the frame. -/
theorem ctFrame_two (F : Addr) {j k : Nat} (hj : j < nW) (hk : k < nW) (m : Mem) (a b : BitVec 64) :
    Frame [⟨F, frameBytes⟩] m ((m.writeW (off F (8 * j)) a).writeW (off F (8 * k)) b) :=
  ((Frame.refl _ m).writeW (List.mem_singleton_self _) a (cF F hj)).writeW
    (List.mem_singleton_self _) b (cF F hk)

theorem ctWindowHead_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {base : Addr} {used total width : Nat}
    (h13 : W 13 = base) (h16 : W 16 = BitVec.ofNat 64 used) (h15 : W 15 = BitVec.ofNat 64 total)
    (hle : used ≤ total) (hmax : total < 2 ^ 64) (hw : width < 2 ^ 31) :
    WP isa (.block [.mov .rax (.mem (sp 104)), .alu .add .rax (.mem (sp 128)), .store (sp 88) .rax,
      .mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (sp 128)),
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 width))]) s fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.gpr .rcx = BitVec.ofNat 64 (total - used) ∧
      t.mem = s.mem.writeW (off F 88) (off base used) ∧ Keep [.rax, .rcx] s t := by
  have hsub : BitVec.ofNat 64 total - BitVec.ofNat 64 used = BitVec.ofNat 64 (total - used) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hmax)] using hle)]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hmax), Nat.mod_eq_of_lt (by omega : total - used < 2 ^ 64)]
  have R1 := R.wf L.geo (k := 11) (by decide) (off base used)
  have r120 : (s.mem.writeW (off F 88) (off base used)).readW (off F 120) 64 = BitVec.ofNat 64 total :=
    R1.slot (d := 120) (k := 15) rfl (by decide) (by simp [upd, h15])
  have r128 : (s.mem.writeW (off F 88) (off base used)).readW (off F 128) 64 = BitVec.ofNat 64 used :=
    R1.slot (d := 128) (k := 16) rfl (by decide) (by simp [upd, h16])
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.gpr .rcx = BitVec.ofNat 64 (total - used) ∧
      t.mem = s.mem.writeW (off F 88) (off base used)) (by
    xrun [ea_sp, L.rsp, L.ld (d := 104) (by decide), L.ld (d := 128) (by decide), L.st (d := 88) (by decide),
      L.ld (d := 120) (by decide),
      R.slot (d := 104) (k := 13) rfl (by decide) h13, R.slot (d := 128) (k := 16) rfl (by decide) h16,
      r120, r128, sx_ofNat hw, hsub]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : total - used < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : width < 2 ^ 64)]) rfl)
    fun _ ⟨⟨hc, hr, hm⟩, hk⟩ => ⟨hc, hr, hm, hk⟩

/-- The window's two words written: the generator search's input over the window. -/
theorem seedGeneratorBefore_windowed {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorBefore n pLen qLen g s)
    (hm : t.mem = (s.mem.writeW (off g.seed.context.geo.F 88) (off g.seed.context.rand.ptr g.seed.used)).writeW
        (off g.seed.context.geo.F 96) (BitVec.ofNat 64 (g.seed.context.ctWindowLen g.seed.used)))
    (hsp : t.gpr .rsp = s.gpr .rsp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    SeedGeneratorBefore n pLen qLen g.windowed t ∧ Frame [⟨g.seed.context.geo.F, frameBytes⟩] s.mem t.mem := by
  obtain ⟨⟨⟨⟨W, hm0, h1, h16, h10⟩, seed, hf, hw, hq⟩, hp, bq⟩, bp, be⟩ := h
  obtain ⟨V, R⟩ := hm0.rep
  have L := hm0.layout
  have fr : Frame [⟨g.seed.context.geo.F, frameBytes⟩] s.mem t.mem := by
    rw [hm]; exact ctFrame_two _ (j := 11) (k := 12) (by decide) (by decide) _ _ _
  have ff : Frame g.seed.context.changed s.mem t.mem := GenerationContext.frame_single fr
  have Rt : Rep t.mem g.seed.context.geo.F g.seed.context.geo.hash V
      (upd (upd W 11 (off g.seed.context.rand.ptr g.seed.used)) 12
        (BitVec.ofNat 64 (g.seed.context.ctWindowLen g.seed.used))) := by
    rw [hm]
    exact (R.wf L.geo (k := 11) (by decide) _).wf L.geo (k := 12) (by decide) _
  have Lt := lay_of_rep L R Rt (by simp [upd]) hsp hwr
  have pn : g.seed.context.geo.pLen ≤ 384 := by rcases g.seed.context.geo.width with hh | hh | hh <;> omega
  have qn : g.seed.context.geo.qLen ≤ 32 := by rcases g.seed.context.geo.qWidth with hh | hh <;> omega
  have rt := hm0.rand.frame ff hrd hwr
  have mt : GenerationMemory g.windowed.seed.context
      (upd (upd W 11 (off g.seed.context.rand.ptr g.seed.used)) 12
        (BitVec.ofNat 64 (g.seed.context.ctWindowLen g.seed.used))) t :=
    { layout := Lt
      rep := ⟨V, Rt⟩
      slots := by
        intro k hk
        by_cases e11 : k = 11
        · subst e11
          simp [upd, SeedGeneratorPublic.windowed, GenerationContext.withHs, GenerationContext.ctWindow,
            GenerationTape.window]
        · by_cases e12 : k = 12
          · subst e12
            simp [upd, SeedGeneratorPublic.windowed, GenerationContext.withHs, GenerationContext.ctWindow,
              GenerationTape.window_length]
          · simp only [upd, e11, e12, ite_false, SeedGeneratorPublic.windowed, GenerationContext.withHs]
            exact hm0.slots k hk
      scratch := hm0.scratch.congr hwr
      seeds := hm0.seeds.frame ff hrd hwr
      hs := rt.window (g.seed.context.ctWindow_fit g.seed.bound)
      rand := rt }
  refine ⟨⟨⟨⟨⟨_, mt, ?_, ?_, ?_⟩, seed.frame ff hrd hwr, hf.congr hsp hwr, hwr.trans hw, hq⟩, hp, ?_⟩, ?_, ?_⟩, fr⟩
  · simpa [upd, SeedGeneratorPublic.windowed] using h1
  · simpa [upd, SeedGeneratorPublic.windowed] using h16
  · simpa [upd, SeedGeneratorPublic.windowed] using h10
  · change Spec.Rsa.bytesAt t.mem (off g.seed.context.geo.B q) g.seed.context.geo.qLen = _
    rw [ctFrame_bytes fr (g.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega))]
    exact bq
  · change Spec.Rsa.bytesAt t.mem (off g.seed.context.geo.B VG.Impl.Dsa.Generation.Layout.p) g.seed.context.geo.pLen = _
    rw [ctFrame_bytes fr (g.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega))]
    exact bp
  · change Spec.Rsa.bytesAt t.mem (off g.seed.context.geo.B exponent) g.seed.context.geo.pLen = _
    rw [ctFrame_bytes fr (g.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega))]
    exact be


theorem ctStoreRcx96_ok {t : State} {F S : Addr} (L : Lay t F S) :
    WP isa (.block [.store (sp 96) .rcx]) t fun u =>
      u.mem = t.mem.writeW (off F 96) (t.gpr .rcx) ∧ Keep [] t u := by
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = t.mem.writeW (off F 96) (t.gpr .rcx)) (by
    xrun [ea_sp, L.rsp, L.st (d := 96) (by decide)]) rfl) fun _ h => h

theorem ctStoreImm96_ok {t : State} {F S : Addr} (L : Lay t F S) {w : Nat} (hw : w < 2 ^ 32) :
    WP isa (.block [.mov32 .rax (.imm (BitVec.ofNat 32 w)), .store (sp 96) .rax]) t fun u =>
      u.mem = t.mem.writeW (off F 96) (BitVec.ofNat 64 w) ∧ Keep [.rax] t u := by
  have hv : (BitVec.ofNat 32 w).setWidth 64 = BitVec.ofNat 64 w := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : w < 4294967296)]
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem.writeW (off F 96) (BitVec.ofNat 64 w)) (by
    xrun [ea_sp, L.rsp, L.st (d := 96) (by decide), hv]) rfl) fun _ h => h

/-- After the window's comparison: its start written, its length in `rcx`
and compared with `windowBytes`. -/
def WindowCheckedFrom (n pLen qLen : Nat) (g : SeedGeneratorPublic) (s t : State) : Prop :=
  SeedGeneratorBefore n pLen qLen g s ∧
    t.cf = some (decide (g.seed.context.rand.bytes.length - g.seed.used <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)) ∧
    t.gpr .rcx = BitVec.ofNat 64 (g.seed.context.rand.bytes.length - g.seed.used) ∧
    t.mem = s.mem.writeW (off g.seed.context.geo.F 88) (off g.seed.context.rand.ptr g.seed.used) ∧
    Keep [.rax, .rcx] s t

def WindowChecked (n pLen qLen : Nat) (g : SeedGeneratorPublic) (t : State) : Prop :=
  ∃ s, WindowCheckedFrom n pLen qLen g s t

theorem windowBytes_lt (pLen : Nat) (hp : pLen ≤ 384) :
    Impl.Dsa.X86_64.Generation.Refill.windowBytes pLen < 2 ^ 31 := by
  unfold Impl.Dsa.X86_64.Generation.Refill.windowBytes; omega

theorem windowHead_ready {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorBefore n pLen qLen g s) :
    WP isa (.block [.mov .rax (.mem (sp 104)), .alu .add .rax (.mem (sp 128)), .store (sp 88) .rax,
      .mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (sp 128)),
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.windowBytes
        g.seed.context.geo.pLen)))]) s (WindowCheckedFrom n pLen qLen g s) := by
  obtain ⟨⟨⟨⟨W, hm, _, h16, _⟩, _⟩, _⟩, _⟩ := id h
  obtain ⟨V, R⟩ := hm.rep
  have pn : g.seed.context.geo.pLen ≤ 384 := by rcases g.seed.context.geo.width with hh | hh | hh <;> omega
  refine WP.mono (ctWindowHead_ok hm.layout R
    ((hm.slots 13 (by simp [generationSlots])).trans g.seed.context.randSlot) h16
    ((hm.slots 15 (by simp [generationSlots])).trans g.seed.context.randLengthSlot)
    g.seed.bound g.seed.context.rand.size (windowBytes_lt _ pn)) fun t ⟨hc, hr, hmem, hk⟩ => ?_
  exact ⟨h, hc, hr, hmem, hk⟩

theorem windowChecked_lay {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorBefore n pLen qLen g s)
    (hm : t.mem = s.mem.writeW (off g.seed.context.geo.F 88) (off g.seed.context.rand.ptr g.seed.used))
    (hk : Keep [.rax, .rcx] s t) : Lay t g.seed.context.geo.F g.seed.context.geo.hash := by
  obtain ⟨⟨⟨⟨W, hm0, _⟩, _⟩, _⟩, _⟩ := h
  obtain ⟨V, R⟩ := hm0.rep
  have Rt : Rep t.mem g.seed.context.geo.F g.seed.context.geo.hash V
      (upd W 11 (off g.seed.context.rand.ptr g.seed.used)) := by
    rw [hm]; exact R.wf hm0.layout.geo (k := 11) (by decide) _
  exact lay_of_rep hm0.layout R Rt (by simp [upd]) (hk.gpr (by decide)) hk.2.2

theorem windowTaken_ready {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (hs : SeedGeneratorBefore n pLen qLen g s)
    (hc : t.cf = some (decide (g.seed.context.rand.bytes.length - g.seed.used <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)))
    (hr : t.gpr .rcx = BitVec.ofNat 64 (g.seed.context.rand.bytes.length - g.seed.used))
    (hm : t.mem = s.mem.writeW (off g.seed.context.geo.F 88) (off g.seed.context.rand.ptr g.seed.used))
    (hk : Keep [.rax, .rcx] s t) (hb : isa.eval .b t = some true) :
    WP isa (.block [.store (sp 96) .rcx]) t fun u =>
      SeedGeneratorBefore n pLen qLen g.windowed u ∧
        Frame [⟨g.seed.context.geo.F, frameBytes⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have short : g.seed.context.rand.bytes.length - g.seed.used <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen := by
    have e : isa.eval .b t = some (decide (g.seed.context.rand.bytes.length - g.seed.used <
        Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)) := by simp only [eval, hc]
    have := hb.symm.trans e
    simpa using this
  refine WP.mono (ctStoreRcx96_ok (windowChecked_lay hs hm hk)) fun u ⟨hu, ku⟩ => ?_
  have len : g.seed.context.ctWindowLen g.seed.used = g.seed.context.rand.bytes.length - g.seed.used := by
    unfold GenerationContext.ctWindowLen; omega
  have hw := seedGeneratorBefore_windowed hs (t := u) (by rw [hu, hm, hr, len])
    ((ku.gpr (by decide)).trans (hk.gpr (by decide))) (ku.2.1.trans hk.2.1) (ku.2.2.trans hk.2.2)
  exact ⟨hw.1, hw.2, ku.2.1.trans hk.2.1, ku.2.2.trans hk.2.2⟩

theorem windowFull_ready {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (hs : SeedGeneratorBefore n pLen qLen g s)
    (hc : t.cf = some (decide (g.seed.context.rand.bytes.length - g.seed.used <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)))
    (hm : t.mem = s.mem.writeW (off g.seed.context.geo.F 88) (off g.seed.context.rand.ptr g.seed.used))
    (hk : Keep [.rax, .rcx] s t) (hb : isa.eval .b t = some false) :
    WP isa (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.windowBytes
        g.seed.context.geo.pLen))), .store (sp 96) .rax]) t fun u =>
      SeedGeneratorBefore n pLen qLen g.windowed u ∧
        Frame [⟨g.seed.context.geo.F, frameBytes⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have full : ¬ g.seed.context.rand.bytes.length - g.seed.used <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen := by
    have e : isa.eval .b t = some (decide (g.seed.context.rand.bytes.length - g.seed.used <
        Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)) := by simp only [eval, hc]
    have := hb.symm.trans e
    simpa using this
  have pn : g.seed.context.geo.pLen ≤ 384 := by rcases g.seed.context.geo.width with hh | hh | hh <;> omega
  refine WP.mono (ctStoreImm96_ok (windowChecked_lay hs hm hk)
    (by have := windowBytes_lt _ pn; omega)) fun u ⟨hu, ku⟩ => ?_
  have len : g.seed.context.ctWindowLen g.seed.used =
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen := by
    unfold GenerationContext.ctWindowLen; omega
  have hw := seedGeneratorBefore_windowed hs (t := u) (by rw [hu, hm, len])
    ((ku.gpr (by decide)).trans (hk.gpr (by decide))) (ku.2.1.trans hk.2.1) (ku.2.2.trans hk.2.2)
  exact ⟨hw.1, hw.2, ku.2.1.trans hk.2.1, ku.2.2.trans hk.2.2⟩

theorem seedGeneratorBefore_pLen {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorBefore n pLen qLen g s) : g.seed.context.geo.pLen = pLen := h.1.2.1

theorem windowChecked_pins (n pLen qLen : Nat) : Pins (WindowChecked n pLen qLen) [.rsp] := by
  intro g s t ⟨s₀, ⟨⟨⟨⟨_, hs, _⟩, _⟩, _⟩, _⟩, _, _, _, hks⟩ ⟨t₀, ⟨⟨⟨⟨_, ht, _⟩, _⟩, _⟩, _⟩, _, _, _, hkt⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [hks.gpr (by decide), hkt.gpr (by decide)]
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem seedGeneratorBefore_pins (n pLen qLen : Nat) : Pins (SeedGeneratorBefore n pLen qLen) [.rsp] := by
  intro g s t ⟨⟨⟨⟨_, hs, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨_, ht, _⟩, _⟩, _⟩, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem window_ct_of (n pLen qLen : Nat)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (sp 104)), .alu .add .rax (.mem (sp 128)),
      .store (sp 88) .rax, .mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (sp 128)),
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.windowBytes pLen)))]) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rsp]) (.block [.store (sp 96) .rcx]) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rsp]) (.block [.mov32 .rax (.imm (BitVec.ofNat 32
      (Impl.Dsa.X86_64.Generation.Refill.windowBytes pLen))), .store (sp 96) .rax]) h₃).isSome = true) :
    RelCT isa (Two (SeedGeneratorBefore n pLen qLen)) (Impl.Dsa.X86_64.Generation.Refill.window pLen)
      (Two fun (g : SeedGeneratorPublic) s => SeedGeneratorBefore n pLen qLen g.windowed s) := by
  unfold Impl.Dsa.X86_64.Generation.Refill.window
  refine RelCT.seq (two_piece (Ψ := WindowChecked n pLen qLen) [.rsp] (seedGeneratorBefore_pins n pLen qLen) t₁
    fun g s h => ?_) ?_
  · have hp := seedGeneratorBefore_pLen h
    subst pLen
    exact WP.mono (windowHead_ready h) fun t ht => ⟨s, ht⟩
  refine two_ite (fun g s t ⟨_, hs, hcs, _⟩ ⟨_, ht, hct, _⟩ => by simp only [eval, hcs, hct]) ?_ ?_
  · refine two_piece [.rsp] (fun g s t hs ht => windowChecked_pins n pLen qLen g s t hs.1 ht.1) t₂
      fun g t ⟨⟨s, hs, hc, hr, hm, hk⟩, hb⟩ => WP.mono (windowTaken_ready hs hc hr hm hk hb) fun _ h => h.1
  · refine two_piece [.rsp] (fun g s t hs ht => windowChecked_pins n pLen qLen g s t hs.1 ht.1) t₃
      fun g t ⟨⟨s, hs, hc, hr, hm, hk⟩, hb⟩ => ?_
    have hp := seedGeneratorBefore_pLen hs
    subst pLen
    exact WP.mono (windowFull_ready hs hc hm hk hb) fun _ h => h.1

theorem window_ct (n pLen qLen : Nat) (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two (SeedGeneratorBefore n pLen qLen)) (Impl.Dsa.X86_64.Generation.Refill.window pLen)
      (Two fun (g : SeedGeneratorPublic) s => SeedGeneratorBefore n pLen qLen g.windowed s) := by
  rcases hp with rfl | rfl | rfl
  all_goals exact window_ct_of n _ qLen (by taint_decide) (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
