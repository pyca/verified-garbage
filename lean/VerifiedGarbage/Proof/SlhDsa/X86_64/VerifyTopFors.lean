module

-- separate module: the calls of forsPk and xmssPk, one stage of the chain of verify's proof

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopLanes
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsCT
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkXmssCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: the calls of `forsPk` and `xmssPk`

Untrusted: everything here is checked by Lean. In `Ctx`, with the lanes'
addresses `a16` set (`Adr`): the callees' precondition (`regions_ok`,
`Ctx.env`), and what their calls leave: `Ctx`, the root at `oMsg`, and
`verify`'s variables (`forsCall_ok`, `xmssCall_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave)

/-- The lanes' addresses. -/
def Adr (L : VL) (m : Mem) (a16 : List Byte) : Prop :=
  ∀ k < 4, bytesAt m (at' L.S (Layout.laneA k + L.n)) 16 = a16 ∧ bytesAt m (at' L.S (Layout.laneB k + L.n)) 16 = a16

variable {L : VL} {g : Reg → BitVec 64} {m₀ : Mem}

theorem Ctx.env {p : Params} (hn : L.n = p.n) {t : State} (hc : Ctx L g m₀ t) {a16 : List Byte} (ha : Adr L t.mem a16) :
    Env p t.mem L.S (bytesAt m₀ L.pk L.n) a16 := by
  refine ⟨hc.rc, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩ <;> rw [← hn]
  exacts [hc.seedA k hk, hc.seedB k hk, (ha k hk).1, (ha k hk).2]

/-! ## What the callees may change -/

/-- A part of `scratch` apart from everything `Ctx` keeps. -/
def OffOk (n o l : Nat) : Prop :=
  o + l ≤ 65536 ∧ (o + l ≤ 1600 ∨ 2368 ≤ o) ∧ (o + l ≤ 3232 ∨ 3232 + n ≤ o) ∧ (o + l ≤ 3264 ∨ 3264 + n ≤ o) ∧
    (o + l ≤ 34080 ∨ 34128 ≤ o) ∧
    ∀ k < 4, (o + l ≤ 3296 + 128 * k ∨ 3296 + 128 * k + n ≤ o) ∧ (o + l ≤ 3808 + 2208 * k ∨ 3808 + 2208 * k + n ≤ o)

theorem free_off (hL : L.Ok) {o l : Nat} (h : OffOk L.n o l) : Free L ⟨at' L.S o, l⟩ := by
  have hn := hL.n32
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine .inl ⟨hL.scr_sub h0, fun q hq => ?_⟩
  simp only [VL.prot, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range] at hq
  rcases hq with ((rfl | rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩)
  · exact Levels.disj_scr L.S (by omega) h0 (by omega)
  · exact Levels.disj_scr L.S (by simp only [Layout.oPkSeed, Layout.oKeys]; omega) h0
      (by simp only [Layout.oPkSeed, Layout.oKeys]; omega)
  · exact Levels.disj_scr L.S (by simp only [Layout.oPkRoot, Layout.oKeys]; omega) h0
      (by simp only [Layout.oPkRoot, Layout.oKeys]; omega)
  · exact Levels.disj_scr L.S (by rw [show oKgSave = 34080 from rfl]; omega) h0
      (by rw [show oKgSave = 34080 from rfl]; omega)
  · have := (h5 k hk).1
    exact Levels.disj_scr L.S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega) h0
      (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
  · have := (h5 k hk).2
    exact Levels.disj_scr L.S (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega) h0
      (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)

theorem free_changes {p : Params} (hL : L.Ok) (hn : L.n = p.n) : ∀ r ∈ changes p L.S, Free L r := by
  have hn32 := hL.n32
  intro r hr
  simp only [changes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range] at hr
  rw [← hn] at hr
  have eV : Layout.oVars = 2400 := rfl
  rcases hr with ((rfl | rfl | rfl) | ⟨k', hk', rfl | rfl⟩) | (rfl | rfl | rfl | rfl | rfl)
  · exact free_off hL (o := 0) (l := 1600) ⟨by omega, by omega, by omega, by omega, by omega,
      fun k hk => ⟨by omega, by omega⟩⟩ |> fun h => by simpa [at'] using h
  · exact free_off hL ⟨by omega, by omega, by omega, by omega, by omega, fun k hk => ⟨by omega, by omega⟩⟩
  · exact free_off hL ⟨by rw [eV]; omega, by rw [eV]; omega, by rw [eV]; omega, by rw [eV]; omega,
      by rw [eV]; omega, fun k hk => ⟨by rw [eV]; omega, by rw [eV]; omega⟩⟩
  · exact free_off hL (by
      simp only [Layout.laneA, Layout.oA, Layout.strideA]
      exact ⟨by omega, by omega, by omega, by omega, by omega, fun k hk => ⟨by omega, by omega⟩⟩)
  · exact free_off hL (by
      simp only [Layout.laneB, Layout.oB, Layout.strideB]
      exact ⟨by omega, by omega, by omega, by omega, by omega, fun k hk => ⟨by omega, by omega⟩⟩)
  all_goals exact free_off hL (by
    simp only [show Layout.oDigits = 30368 from rfl, show Layout.oN = 12640 from rfl, show Layout.nodeSlots = 520 from rfl,
      show Layout.oRoots = 29280 from rfl, show Layout.oMsg = 30496 from rfl, show Layout.oFidx = 31328 from rfl]
    exact ⟨by omega, by omega, by omega, by omega, by omega, fun k hk => ⟨by omega, by omega⟩⟩)

/-! ## The callees' regions -/

theorem empty_disj (S : Addr) (r : Region) : Region.Disjoint ⟨S, 0⟩ r := fun _ h _ => by
  simp [Region.Contains] at h

theorem below8 (sp : Addr) : (⟨sp - 8, 8⟩ : Region) = below sp 8 := rfl

theorem ret_cs (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) :
    Region.Sub (retR (t.callEntry.withRegions rd wr)) L.CS := by
  have hst := hL.st16
  show Region.Sub ⟨(t.callEntry.withRegions rd wr).gpr .rsp, 8⟩ L.CS
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.rsp, below8, below_SP (by omega)]
  exact Offset.sub_base _ (by omega)

theorem stk_cs (_hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) :
    Region.Sub (below ((t.callEntry.withRegions rd wr).gpr .rsp) L.st) L.CS := by
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.rsp]
  refine fun a h => ?_
  have := below_callee L.SP L.st a h
  rw [below_SP (Nat.le_refl _)] at this
  simpa using this

theorem regions_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {R : Region} (hR : Region.Sub R L.SIG)
    (hRf : R.base.toNat + R.len ≤ 2 ^ 64) :
    Regions L.st (t.callEntry.withRegions [R] [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]) L.S [R] ⟨L.S, 0⟩ := by
  have rs := ret_cs hL hc [R] [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]
  have ks := stk_cs hL hc [R] [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]
  have csk : Region.Sub L.CS L.STK := Region.sub_prefix (by omega)
  have rR : L.SIG.Disjoint L.SCR := hL.sSig.symm
  refine ⟨rfl, rfl, hL.nS, by show L.S.toNat + 0 ≤ 2 ^ 64; have := hL.nS; omega, empty_disj _ _, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hRf, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact rR.sub_left hR,
    hL.cs_scr.sub_left rs, (empty_disj _ _).symm, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hL.kSig.sub_left (fun a h => csk a (rs a h))).sub_right hR,
    hL.cs_scr.sub_left ks, (empty_disj _ _).symm, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hL.kSig.sub_left (fun a h => csk a (ks a h))).sub_right hR⟩

theorem covers_call {t : State} (hc' : Ctx L g m₀ t) {R : Region}
    (hR : InRegions L.rd R.base R.len) :
    Covers ([R] ++ [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]) (t.rd ++ t.wr) ∧ Covers [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩] t.wr := by
  have hw : Covers [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩] t.wr := by
    rw [hc'.wr]
    refine Covers.of_sub fun r hr => ⟨L.SCR, by simp, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, by simp, by simp [scratchLen]⟩
    · exact ⟨0, by simp, by simp⟩
  refine ⟨Covers.append_left ?_ (Covers.right hw), hw⟩
  rw [hc'.rd]
  exact Covers.left (Covers.one hR)

/-! ## After a call -/

theorem changes_vars {p : Params} (hn : L.n = p.n) (hn32 : L.n ≤ 32) :
    ∀ r ∈ changes p L.S, r.Disjoint ⟨at' L.S (oKgSave + 48), 32⟩ := by
  intro r hr
  simp only [changes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range] at hr
  rw [← hn] at hr
  have eK : oKgSave = 34080 := rfl
  rcases hr with ((rfl | rfl | rfl) | ⟨k', hk', rfl | rfl⟩) | (rfl | rfl | rfl | rfl | rfl)
  · exact Offset.base_disjoint L.S (by rw [eK]; omega) (by rw [eK]; omega)
  all_goals refine Levels.disj_scr L.S ?_ ?_ (by rw [eK]; omega) <;>
    (try simp only [eK, show Layout.oVars = 2400 from rfl, show Layout.oDigits = 30368 from rfl,
      show Layout.oN = 12640 from rfl, show Layout.nodeSlots = 520 from rfl, show Layout.oRoots = 29280 from rfl,
      show Layout.oMsg = 30496 from rfl, show Layout.oFidx = 31328 from rfl, Layout.laneA, Layout.oA, Layout.strideA,
      Layout.laneB, Layout.oB, Layout.strideB]) <;> omega

/-- The memory of the call's entry. -/
theorem ce_frame {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) :
    Frame [below L.SP 8] t.mem (t.callEntry.withRegions rd wr).mem := by
  rw [State.withRegions_mem, State.callEntry_mem, ← hc.rsp]
  exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- A call's entry, as a state of the frame. -/
theorem ce_ctx (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) :
    Ctx L g m₀ { t with mem := (t.callEntry.withRegions rd wr).mem } :=
  hc.of_frame hL rfl rfl rfl rfl (fun _ _ _ _ => rfl) (ce_frame hc rd wr) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact free_below hL (by have := hL.st16; omega)

/-- After a call that changes at most `changes` and its stack. -/
theorem after_call {p : Params} (hL : L.Ok) (hn : L.n = p.n) {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region}
    {s' : State} (hrd : s'.rd = t.rd) (hwr : s'.wr = t.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = t.gpr r)
    (hf : Frame (changes p L.S ++ [below ((t.callEntry.withRegions rd wr).gpr .rsp) L.st])
      (t.callEntry.withRegions rd wr).mem s'.mem) :
    Ctx L g m₀ s' ∧ ∀ i < 4, s'.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64 := by
  have hn32 := hL.n32
  have hst := hL.st16
  have fr : Frame (below L.SP 8 :: (changes p L.S ++ [below ((t.callEntry.withRegions rd wr).gpr .rsp) L.st]))
      t.mem s'.mem :=
    ((ce_frame hc rd wr).mono fun r hr => by simp at hr; simp [hr]).trans (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
  have free : ∀ r ∈ below L.SP 8 :: (changes p L.S ++ [below ((t.callEntry.withRegions rd wr).gpr .rsp) L.st]),
      Free L r := by
    intro r hr
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr | rfl
    · exact free_below hL (by omega)
    · exact free_changes hL hn r hr
    · exact .inr (stk_cs hL hc rd wr)
  refine ⟨hc.called hL hrd hwr hcs fr free, fun i hi => Thash4Avx.readW_frame fr fun r hr => ?_⟩
  have hv : Region.Sub ⟨L.var i, 8⟩ L.SCR := fun a h => hL.scr_sub (o := oKgSave + 48) (l := 32)
    (by rw [show oKgSave = 34080 from rfl]; omega) a (var_sub hL hi a h)
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · rw [below_SP (by omega)]
    exact (hL.cs_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left hv
  · exact ((changes_vars hn hn32 r hr).symm.sub_left (var_sub hL hi))
  · exact (hL.cs_scr.sub_left (stk_cs hL hc rd wr)).symm.sub_left hv

/-- Bytes of `scratch` at a call's entry. -/
theorem ce_scr (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) {o l : Nat} (h : o + l ≤ 65536) :
    bytesAt (t.callEntry.withRegions rd wr).mem (at' L.S o) l = bytesAt t.mem (at' L.S o) l :=
  bytesAt_frame (ce_frame hc rd wr) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [below_SP (by have := hL.st16; omega)]
    exact (hL.cs_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (hL.scr_sub h)) (by omega)

/-- Bytes of the signature at a call's entry. -/
theorem ce_sig (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) {o l : Nat} (h : o + l ≤ L.sigL) :
    bytesAt (t.callEntry.withRegions rd wr).mem (L.sig + BitVec.ofNat 64 o) l = bytesAt m₀ (L.sig + BitVec.ofNat 64 o) l := by
  have hS : Region.Sub ⟨L.sig + BitVec.ofNat 64 o, l⟩ L.SIG := Offset.sub_base _ h
  have hst := hL.st16
  rw [bytesAt_frame (ce_frame hc rd wr) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [below_SP (by omega)]
    exact (hL.kSig.sub_left (Offset.sub_base _ (by omega))).symm.sub_left hS) (by have := hL.nSig; omega)]
  exact hc.bytesAt_eq (hL.sSig.sub_right hS) (hL.kSig.sub_right hS) (by have := hL.nSig; omega)

theorem adr_ce (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) {a16 : List Byte}
    (ha : Adr L t.mem a16) : Adr L (t.callEntry.withRegions rd wr).mem a16 := fun k hk => by
  have hn := hL.n32
  rw [ce_scr hL hc rd wr (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega),
    ce_scr hL hc rd wr (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)]
  exact ha k hk

/-! ## `forsPk` -/

/-- `forsPk`'s precondition at a call's entry. -/
theorem fors_pre {p : Params} (hp : VPar p) (hL : L.Ok) (hn : L.n = p.n) (hsl : p.n + p.forsSigLen ≤ L.sigL) {t : State}
    (hc : Ctx L g m₀ t) {a16 : List Byte} (ha : Adr L t.mem a16) {kp : Nat} (hkp : kp < 2 ^ 32)
    (h1 : t.gpr .rdi = L.S) (h2 : t.gpr .rsi = L.sig + BitVec.ofNat 64 p.n) (h3 : t.gpr .rdx = BitVec.ofNat 64 kp) :
    (forsPkContract p L.st).pre (t.callEntry.withRegions [⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]
      [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]) ∧
    Covers ([⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩] ++ [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]) (t.rd ++ t.wr) ∧
    Covers [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩] t.wr := by
  let rd : List Region := [⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]
  let wr : List Region := [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]
  have e1 : (t.callEntry.withRegions rd wr).gpr .rdi = L.S := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h1]
  have e2 : (t.callEntry.withRegions rd wr).gpr .rsi = L.sig + BitVec.ofNat 64 p.n := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h2]
  have e3 : (t.callEntry.withRegions rd wr).gpr .rdx = BitVec.ofNat 64 kp := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h3]
  have hkp' : (BitVec.ofNat 64 kp).toNat = kp := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : Region.Sub ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩ L.SIG := Offset.sub_base _ hsl
  have hfit : (L.sig + BitVec.ofNat 64 p.n).toNat + p.forsSigLen ≤ 2 ^ 64 := by
    have := hL.nSig
    have := hp.fpos
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.n) (by have := hp.n; omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have env := (ce_ctx hL hc rd wr).env hn (adr_ce hL hc rd wr ha)
  have hpre : (forsPkContract p L.st).pre (t.callEntry.withRegions rd wr) := by
    simp only [forsPkContract, e1, e3, hkp']
    exact ⟨by rw [e2]; exact regions_ok hL hc hsub hfit, ⟨_, _, env⟩, hkp⟩
  obtain ⟨hcov, hcovw⟩ := covers_call (R := ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩) hc
    ⟨L.SIG, by simp, Offset.contains_base _ hsl (by have := hp.n; omega)⟩
  exact ⟨hpre, hcov, hcovw⟩

/-- `xmssPk`'s precondition at a call's entry. -/
theorem xmss_pre {p : Params} (hp : VPar p) (hL : L.Ok) (hn : L.n = p.n) {o : Nat}
    (hsl : o + p.xmssSigLen ≤ L.sigL) {t : State} (hc : Ctx L g m₀ t) {a16 : List Byte} (ha : Adr L t.mem a16)
    {idx : Nat} (hidx : idx < 2 ^ p.hp) (h1 : t.gpr .rdi = L.S) (h2 : t.gpr .rsi = BitVec.ofNat 64 idx)
    (h3 : t.gpr .rdx = L.sig + BitVec.ofNat 64 o) :
    (xmssPkContract p L.st).pre (t.callEntry.withRegions [⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩]
      [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]) ∧
    Covers ([⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩] ++ [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]) (t.rd ++ t.wr) ∧
    Covers [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩] t.wr := by
  have hhp := hp.hp9
  have hidx' : idx < 2 ^ 64 := Nat.lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) (by omega))
  let rd : List Region := [⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩]
  let wr : List Region := [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]
  have e1 : (t.callEntry.withRegions rd wr).gpr .rdi = L.S := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h1]
  have e2 : (t.callEntry.withRegions rd wr).gpr .rsi = BitVec.ofNat 64 idx := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h2]
  have e3 : (t.callEntry.withRegions rd wr).gpr .rdx = L.sig + BitVec.ofNat 64 o := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h3]
  have hidx'' : (BitVec.ofNat 64 idx).toNat = idx := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx']
  have hsub : Region.Sub ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩ L.SIG := Offset.sub_base _ hsl
  have hfit : (L.sig + BitVec.ofNat 64 o).toNat + p.xmssSigLen ≤ 2 ^ 64 := by
    have := hL.nSig
    have := hp.xpos
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have env := (ce_ctx hL hc rd wr).env hn (adr_ce hL hc rd wr ha)
  obtain ⟨hcov, hcovw⟩ := covers_call (R := ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩) hc
    ⟨L.SIG, by simp, Offset.contains_base _ hsl (by have := hL.nSig; have := hp.xpos; omega)⟩
  have hpre : (xmssPkContract p L.st).pre (t.callEntry.withRegions rd wr) := by
    simp only [xmssPkContract, e1, e2, hidx'']
    exact ⟨by rw [e3]; exact regions_ok hL hc hsub hfit, ⟨_, _, env⟩, hidx⟩
  exact ⟨hpre, hcov, hcovw⟩

theorem forsCall_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hp : VPar p) (hmx : (Impl.SlhDsa.X86_64.Verify.forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Impl.SlhDsa.X86_64.Verify.forsPk p f)) (hst : T.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n)
    (hsl : p.n + p.forsSigLen ≤ L.sigL) {t : State} (hc : Ctx L g m₀ t) {a16 : List Byte} (ha : Adr L t.mem a16)
    {kp : Nat} (hkp : kp < 2 ^ 32) (h1 : t.gpr .rdi = L.S) (h2 : t.gpr .rsi = L.sig + BitVec.ofNat 64 p.n)
    (h3 : t.gpr .rdx = BitVec.ofNat 64 kp) (name : String) :
    WP isa (.call name (Impl.SlhDsa.X86_64.Verify.forsPk p f)) t fun t' => Ctx L g m₀ t' ∧
      (∀ i < 4, t'.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64) ∧
      bytesAt t'.mem (at' L.S Layout.oMsg) p.n = forsPkFromSig p (bytesAt m₀ (L.sig + BitVec.ofNat 64 p.n) p.forsSigLen)
        (mdAt p t.mem L.S) (bytesAt m₀ L.pk L.n) (forsAdrs a16 kp) := by
  have hn32 := hL.n32
  let rd : List Region := [⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]
  let wr : List Region := [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]
  have e1 : (t.callEntry.withRegions rd wr).gpr .rdi = L.S := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h1]
  have e2 : (t.callEntry.withRegions rd wr).gpr .rsi = L.sig + BitVec.ofNat 64 p.n := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h2]
  have e3 : (t.callEntry.withRegions rd wr).gpr .rdx = BitVec.ofNat 64 kp := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h3]
  have hkp' : (BitVec.ofNat 64 kp).toNat = kp := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : Region.Sub ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩ L.SIG := Offset.sub_base _ hsl
  have hfit : (L.sig + BitVec.ofNat 64 p.n).toNat + p.forsSigLen ≤ 2 ^ 64 := by
    have := hL.nSig
    have := hp.fpos
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.n) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have env := (ce_ctx hL hc rd wr).env hn (adr_ce hL hc rd wr ha)
  have hpre : (forsPkContract p L.st).pre (t.callEntry.withRegions rd wr) := by
    simp only [forsPkContract, e1, e3, hkp']
    exact ⟨by rw [e2]; exact regions_ok hL hc hsub hfit, ⟨_, _, env⟩, hkp⟩
  obtain ⟨hcov, hcovw⟩ := covers_call (R := ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩) hc
    ⟨L.SIG, by simp, Offset.contains_base _ hsl (by omega)⟩
  refine forsPkcall_ok T ht hp.fpar hst (by have := hL.st62; omega) hmx hsp name hpre hcov hcovw
    fun s' hrd hwr hcs _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_
  simp only [forsPkContract, e1, e2, e3, hkp'] at hpost
  obtain ⟨_, hmsg, hfr⟩ := hpost _ _ env
  rw [hm₂] at hmsg hfr
  obtain ⟨hc', hv⟩ := after_call hL hn hc hrd hwr hcs hfr
  refine ⟨hc', hv, ?_⟩
  rw [hmsg, ce_sig hL hc rd wr hsl]
  congr 1
  exact ce_scr hL hc rd wr (by
    have := hp.m64; simp only [show Layout.oDigest = 30304 from rfl]; have := hp.fpar.md; omega)

/-! ## `xmssPk` -/

theorem xmssCall_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hp : VPar p) (hst : T.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n) {o : Nat} (hsl : o + p.xmssSigLen ≤ L.sigL)
    {t : State} (hc : Ctx L g m₀ t) {a16 : List Byte} (ha : Adr L t.mem a16) {idx : Nat} (hidx : idx < 2 ^ p.hp)
    (h1 : t.gpr .rdi = L.S) (h2 : t.gpr .rsi = BitVec.ofNat 64 idx) (h3 : t.gpr .rdx = L.sig + BitVec.ofNat 64 o)
    (name : String) :
    WP isa (.call name (Impl.SlhDsa.X86_64.Verify.xmssPk p f)) t fun t' => Ctx L g m₀ t' ∧
      (∀ i < 4, t'.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64) ∧
      bytesAt t'.mem (at' L.S Layout.oMsg) p.n = xmssPkFromSig p idx (bytesAt m₀ (L.sig + BitVec.ofNat 64 o) p.xmssSigLen)
        (bytesAt t.mem (at' L.S Layout.oMsg) p.n) (bytesAt m₀ L.pk L.n) (Proof.SlhDsa.treeAdrs a16) := by
  have hn32 := hL.n32
  have hhp := hp.hp9
  have hidx' : idx < 2 ^ 64 := Nat.lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) (by omega))
  let rd : List Region := [⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩]
  let wr : List Region := [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]
  have e1 : (t.callEntry.withRegions rd wr).gpr .rdi = L.S := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h1]
  have e2 : (t.callEntry.withRegions rd wr).gpr .rsi = BitVec.ofNat 64 idx := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h2]
  have e3 : (t.callEntry.withRegions rd wr).gpr .rdx = L.sig + BitVec.ofNat 64 o := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h3]
  have hidx'' : (BitVec.ofNat 64 idx).toNat = idx := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx']
  have hsub : Region.Sub ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩ L.SIG := Offset.sub_base _ hsl
  have hfit : (L.sig + BitVec.ofNat 64 o).toNat + p.xmssSigLen ≤ 2 ^ 64 := by
    have := hL.nSig
    have := hp.xpos
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have env := (ce_ctx hL hc rd wr).env hn (adr_ce hL hc rd wr ha)
  have hpre : (xmssPkContract p L.st).pre (t.callEntry.withRegions rd wr) := by
    simp only [xmssPkContract, e1, e2, hidx'']
    exact ⟨by rw [e3]; exact regions_ok hL hc hsub hfit, ⟨_, _, env⟩, hidx⟩
  obtain ⟨hcov, hcovw⟩ := covers_call (R := ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩) hc
    ⟨L.SIG, by simp, Offset.contains_base _ hsl (by have := hL.nSig; have := hp.xpos; omega)⟩
  refine XmssCT.xmssPkcall_ok T ht hp.n hp.fam hp.w4 hp.hp1 (by omega) hst (by have := hL.st62; omega)
    (by rw [← ht]; rw [ht]; exact T.nomx) name hpre hcov hcovw
    fun s' hrd hwr hcs _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_
  simp only [xmssPkContract, e1, e2, e3, hidx''] at hpost
  obtain ⟨_, hmsg, hfr⟩ := hpost _ _ env
  rw [hm₂] at hmsg hfr
  obtain ⟨hc', hv⟩ := after_call hL hn hc hrd hwr hcs hfr
  refine ⟨hc', hv, ?_⟩
  rw [hmsg, ce_sig hL hc rd wr hsl, ce_scr hL hc rd wr (by simp only [show Layout.oMsg = 30496 from rfl]; omega)]

/-! ## The lanes' addresses -/

theorem lanesR_scr {L : VL} (hL : L.Ok) : Region.Sub (KeyGen.lanesR L.S) L.SCR := hL.scr_sub (by
  simp only [Layout.oA]; omega)

/-- Writes in the lanes that keep their `PK.seed` keep `Ctx`. -/
theorem Ctx.of_lanes (hL : L.Ok) {t t' : State} (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hg : ∀ r, r ≠ .rax → r ≠ .r11 → t'.gpr r = t.gpr r) (hf : Frame [KeyGen.lanesR L.S] t.mem t'.mem)
    (hsA : ∀ k < 4, bytesAt t'.mem (at' L.S (Layout.laneA k)) L.n = bytesAt t.mem (at' L.S (Layout.laneA k)) L.n)
    (hsB : ∀ k < 4, bytesAt t'.mem (at' L.S (Layout.laneB k)) L.n = bytesAt t.mem (at' L.S (Layout.laneB k)) L.n) :
    Ctx L g m₀ t' := by
  have hn := hL.n32
  have eA : Layout.oA = 3296 := rfl
  have dl : ∀ {o l : Nat}, o + l ≤ 65536 → (o + l ≤ 3296 ∨ 12640 ≤ o) → ∀ r ∈ [KeyGen.lanesR L.S],
      Region.Disjoint ⟨at' L.S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Levels.disj_scr L.S (by rw [eA]; omega) h₁ (by rw [eA]; omega)
  have dF : ∀ d, d + 8 ≤ 72 → ∀ r ∈ [KeyGen.lanesR L.S], Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, 8⟩ r :=
    fun d hd r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.fr_scr hd).sub_right (lanesR_scr hL)
  have keepF : ∀ d, d + 8 ≤ 72 →
      t'.mem.readW (L.SP + BitVec.ofNat 64 d) 64 = t.mem.readW (L.SP + BitVec.ofNat 64 d) 64 :=
    fun d hd => Thash4Avx.readW_frame hf (dF d hd)
  have eK : oKgSave = 34080 := rfl
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide) (by decide)).trans hc.rsp,
    (hg .rbx (by decide) (by decide)).trans hc.rbx, fun r hr h1 h2 => ?_, fun i hi => ?_,
    (keepF 8 (by omega)).trans hc.pScr, (keepF 16 (by omega)).trans hc.pSig, (keepF 24 (by omega)).trans hc.pSigL,
    (keepF 32 (by omega)).trans hc.pCtxLen, (keepF 40 (by omega)).trans hc.pCtx, (keepF 48 (by omega)).trans hc.pLen,
    (keepF 56 (by omega)).trans hc.pMsg, (keepF 64 (by omega)).trans hc.pKey, ?_,
    hc.frame.trans (Frame.sub hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨L.SCR, by simp, lanesR_scr hL⟩),
    fun r hr k hk => ?_, ?_, ?_, fun k hk => (hsA k hk).trans (hc.seedA k hk), fun k hk => (hsB k hk).trans (hc.seedB k hk)⟩
  · rw [hg r (by intro e; subst e; revert hr; decide) (by intro e; subst e; revert hr; decide)]
    exact hc.cs r hr h1 h2
  · rw [Thash4Avx.readW_frame hf (dl (o := oKgSave + 8 * i) (by rw [eK]; omega) (by rw [eK]; omega))]
    exact hc.saved i hi
  · rw [bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := (hL.fr_scr (d := 0) (n := 2) (by omega)).sub_right (lanesR_scr hL)
      simpa using this) (by omega)]
    exact hc.hdr
  · rw [Thash4Avx.readW_frame hf (dl (o := 1600 + 32 * r + 8 * k) (by omega) (by omega))]
    exact hc.rc r hr k hk
  · rw [bytesAt_frame hf (dl (by simp only [Layout.oPkSeed, Layout.oKeys]; omega)
      (by simp only [Layout.oPkSeed, Layout.oKeys]; omega)) (by omega)]
    exact hc.kSeed
  · rw [bytesAt_frame hf (dl (by simp only [Layout.oPkRoot, Layout.oKeys]; omega)
      (by simp only [Layout.oPkRoot, Layout.oKeys]; omega)) (by omega)]
    exact hc.kRoot

/-- `treeLanes` with the layer `j` in `r10` and the tree `T` in `r9`. -/
theorem lanes_ok {p : Params} (hL : L.Ok) (hn : L.n = p.n) {j T : Nat} (hj : j < 2 ^ 32) (hT : T < 2 ^ 64)
    {s : State} (hc : Ctx L g m₀ s) (h10 : (s.gpr .r10).toNat = j) (h9 : s.gpr .r9 = BitVec.ofNat 64 T)
    {Q : State → Prop}
    (k : ∀ u, Ctx L g m₀ u → (∀ r, r ≠ .rax → r ≠ .r11 → u.gpr r = s.gpr r) →
      Adr L u.mem (Proof.SlhDsa.layerTree j T) → Frame [KeyGen.lanesR L.S] s.mem u.mem → Q u) :
    WP isa (.block (Impl.SlhDsa.X86_64.Shake.treeLanes p .r10 .r9)) s Q := by
  have hn32 := hL.n32
  refine treeG_ok (by omega) hj hT hc.rbx hc.inScr h10 h9 fun t u hg ⟨hg', rd, wr, ad, sd, f⟩ hm hr hw => ?_
  rw [hm] at sd f
  have hgu : ∀ r, r ≠ .rax → r ≠ .r11 → u.gpr r = s.gpr r := hg
  refine k u (hc.of_lanes hL (by rw [rd, hr]) (by rw [wr, hw]) hgu f (fun k hk => ?_) (fun k hk => ?_)) hgu
    (fun k hk => ⟨?_, ?_⟩) f
  · have := sd k hk 0 (by decide); rw [hn]; simpa [KeyGen.lane] using this
  · have := sd k hk 1 (by decide); rw [hn]; simpa [KeyGen.lane] using this
  · have := ad k hk 0 (by decide) (by omega); rw [hn]; simpa [KeyGen.lane] using this
  · have := ad k hk 1 (by decide) (by omega); rw [hn]; simpa [KeyGen.lane] using this

end VG.Proof.SlhDsa.X86_64.VerifyTop
