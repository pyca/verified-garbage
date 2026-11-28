module

-- separate module: the calls of `forsSign` and `xmssTree`, apart from the frame's blocks

public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopIdx
public import VerifiedGarbage.Proof.SlhDsa.X86_64.XmssCT
public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopHash
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsGroup
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsHeight
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkPath

/-!
# SLH-DSA (SHAKE) on x86-64, `sign`: the calls of `forsSign` and `xmssTree`

Untrusted: everything here is checked by Lean. In `Ctx`, with the lanes'
addresses `a16` set (`Adr`): the callees' precondition (`regions_ok`,
`Ctx.env`), and what their calls leave: `Ctx`, their signature and root,
`sign`'s variables, and the rest of the signature (`forsCall_ok`,
`xmssCall_ok`). The FORS signing function is any code `forsSign` proven
against `forsContract` (`ForsFn`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave)

/-- The lanes' addresses. -/
def Adr (L : SL) (m : Mem) (a16 : List Byte) : Prop :=
  ∀ k < 4, bytesAt m (at' L.S (Layout.laneA k + L.n)) 16 = a16 ∧ bytesAt m (at' L.S (Layout.laneB k + L.n)) 16 = a16

variable {L : SL} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `PK.seed`, from the private key on entry. -/
abbrev SL.pkSeed (L : SL) (m₀ : Mem) : List Byte := bytesAt m₀ (L.sk + BitVec.ofNat 64 (L.n * 2)) L.n
/-- `SK.seed`, likewise. -/
abbrev SL.skSeed (L : SL) (m₀ : Mem) : List Byte := bytesAt m₀ (L.sk + BitVec.ofNat 64 (L.n * 0)) L.n

theorem Ctx.env {p : Params} (hn : L.n = p.n) {t : State} (hc : Ctx L g m₀ t) {a16 : List Byte} (ha : Adr L t.mem a16) :
    Env p t.mem L.S (L.pkSeed m₀) a16 := by
  refine ⟨hc.rc, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩ <;> rw [← hn]
  exacts [hc.seedA k hk, hc.seedB k hk, (ha k hk).1, (ha k hk).2]

theorem Ctx.skAt {p : Params} (hn : L.n = p.n) {t : State} (hc : Ctx L g m₀ t) : SkAt p t.mem L.S (L.skSeed m₀) := by
  have := hc.keys 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at this
  show bytesAt t.mem (at' L.S Layout.oKeys) p.n = bytesAt m₀ (L.sk + BitVec.ofNat 64 (L.n * 0)) L.n
  rw [← hn]; exact this

/-! ## What the callees may change -/

/-- The stack below `SP`. -/
theorem below_SP {k : Nat} (hk : k ≤ L.st + 8) :
    below L.SP k = ⟨L.B + BitVec.ofNat 64 (L.st + 8 - k), k⟩ := by
  show (⟨L.SP - BitVec.ofNat 64 k, k⟩ : Region) = _
  congr 1
  rw [SL.SP, Offset.sub_ofNat_eq _ (a := k) (b := L.st + 8) hk, BitVec.add_sub_cancel]

theorem free_below (_hL : L.Ok) {k : Nat} (hk : k ≤ L.st + 8) : Free L (below L.SP k) := by
  rw [below_SP hk]
  exact .inr (.inl (Offset.sub_base _ (by omega)))

/-- A part of `scratch` apart from everything `Ctx` keeps. -/
def OffOk (n o l : Nat) : Prop :=
  o + l ≤ 65536 ∧ (o + l ≤ 1600 ∨ 2368 ≤ o) ∧ (o + l ≤ 3168 ∨ 3296 ≤ o) ∧
    (o + l ≤ 34080 ∨ 34128 ≤ o) ∧
    ∀ k < 4, (o + l ≤ 3296 + 128 * k ∨ 3296 + 128 * k + n ≤ o) ∧ (o + l ≤ 3808 + 2208 * k ∨ 3808 + 2208 * k + n ≤ o)

theorem free_off (hL : L.Ok) {o l : Nat} (h : OffOk L.n o l) : Free L ⟨at' L.S o, l⟩ := by
  have hn := hL.n32
  obtain ⟨h0, h1, h2, h4, h5⟩ := h
  refine .inl ⟨hL.scr_sub h0, fun q hq => ?_⟩
  simp only [SL.prot, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range] at hq
  rcases hq with ((rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩)
  · exact Levels.disj_scr L.S (by omega) h0 (by omega)
  · exact Levels.disj_scr L.S (by simp only [Layout.oKeys]; omega) h0 (by simp only [Layout.oKeys]; omega)
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
  · exact free_off hL (o := 0) (l := 1600) ⟨by omega, by omega, by omega, by omega,
      fun k hk => ⟨by omega, by omega⟩⟩ |> fun h => by simpa [at'] using h
  · exact free_off hL ⟨by omega, by omega, by omega, by omega, fun k hk => ⟨by omega, by omega⟩⟩
  · exact free_off hL ⟨by rw [eV]; omega, by rw [eV]; omega, by rw [eV]; omega, by rw [eV]; omega,
      fun k hk => ⟨by rw [eV]; omega, by rw [eV]; omega⟩⟩
  · exact free_off hL (by
      simp only [Layout.laneA, Layout.oA, Layout.strideA]
      exact ⟨by omega, by omega, by omega, by omega, fun k hk => ⟨by omega, by omega⟩⟩)
  · exact free_off hL (by
      simp only [Layout.laneB, Layout.oB, Layout.strideB]
      exact ⟨by omega, by omega, by omega, by omega, fun k hk => ⟨by omega, by omega⟩⟩)
  all_goals exact free_off hL (by
    simp only [show Layout.oDigits = 30368 from rfl, show Layout.oN = 12640 from rfl, show Layout.nodeSlots = 520 from rfl,
      show Layout.oRoots = 29280 from rfl, show Layout.oMsg = 30496 from rfl, show Layout.oFidx = 31328 from rfl]
    exact ⟨by omega, by omega, by omega, by omega, fun k hk => ⟨by omega, by omega⟩⟩)

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

/-! ## The callees' regions -/

theorem ret_cs (hst : 8 ≤ L.st) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) :
    Region.Sub (retR (t.callEntry.withRegions rd wr)) L.CS := by
  show Region.Sub ⟨(t.callEntry.withRegions rd wr).gpr .rsp, 8⟩ L.CS
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.rsp, show (⟨L.SP - 8, 8⟩ : Region) = below L.SP 8 from rfl,
    below_SP (by omega)]
  exact Offset.sub_base _ (by omega)

theorem stk_cs {k : Nat} (hk : k ≤ L.st) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) :
    Region.Sub (below ((t.callEntry.withRegions rd wr).gpr .rsp) k) L.CS := by
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.rsp]
  refine fun a h => ?_
  have := below_callee L.SP k a h
  rw [below_SP (by omega)] at this
  exact Offset.sub_base _ (by omega) a this

/-- The regions of a callee that writes `R`, a part of the signature. -/
theorem regions_ok (hL : L.Ok) {k : Nat} (hk : k ≤ L.st) (hst : 8 ≤ L.st) {t : State} (hc : Ctx L g m₀ t)
    {R : Region} (hR : Region.Sub R L.SIG) (hRf : R.base.toNat + R.len ≤ 2 ^ 64) :
    Regions k (t.callEntry.withRegions [] [⟨L.S, scratchLen⟩, R]) L.S [] R := by
  have rs := ret_cs hst hc [] [⟨L.S, scratchLen⟩, R]
  have ks := stk_cs hk hc [] [⟨L.S, scratchLen⟩, R]
  have rR : R.Disjoint ⟨L.S, Layout.oSigTmp⟩ :=
    (hL.sSig.symm.sub_left hR).sub_right (Region.sub_prefix (by simp only [show Layout.oSigTmp = 31648 from rfl]; omega))
  refine ⟨rfl, rfl, hL.nS, hRf, rR, fun r hr => absurd hr List.not_mem_nil, fun r hr => absurd hr List.not_mem_nil,
    hL.cs_scr.sub_left rs, (hL.cs_sig.sub_left rs).sub_right hR, fun r hr => absurd hr List.not_mem_nil,
    hL.cs_scr.sub_left ks, (hL.cs_sig.sub_left ks).sub_right hR, fun r hr => absurd hr List.not_mem_nil⟩

theorem covers_call {t : State} (hc : Ctx L g m₀ t) {R : Region} (hR : InRegions [L.SIG] R.base R.len) :
    Covers ([] ++ [⟨L.S, scratchLen⟩, R]) (t.rd ++ t.wr) ∧ Covers [⟨L.S, scratchLen⟩, R] t.wr := by
  have hw : Covers [⟨L.S, scratchLen⟩, R] t.wr := by
    rw [hc.wr]
    refine Covers.cons (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [scratchLen]) (Covers.cons ?_ Covers.nil)
    exact (Covers.one hR).trans (Covers.of_mem fun r hr => by simp at hr; subst hr; simp)
  exact ⟨by rw [List.nil_append]; exact Covers.right hw, hw⟩

/-! ## After a call -/

/-- The memory of the call's entry. -/
theorem ce_frame {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) :
    Frame [below L.SP 8] t.mem (t.callEntry.withRegions rd wr).mem := by
  rw [State.withRegions_mem, State.callEntry_mem, ← hc.rsp]
  exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem Ctx.called (hL : L.Ok) {t t' : State} (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hrs : ∀ r ∈ rs, Free L r) : Ctx L g m₀ t' :=
  hc.of_frame hL hrd hwr (hcs .rsp (by decide)) (hcs .rbx (by decide)) (fun r hr _ _ => hcs r hr) hf hrs

/-- A call's entry, as a state of the frame. -/
theorem ce_ctx (hL : L.Ok) (hst : 8 ≤ L.st) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) :
    Ctx L g m₀ { t with mem := (t.callEntry.withRegions rd wr).mem } :=
  hc.of_frame hL rfl rfl rfl rfl (fun _ _ _ _ => rfl) (ce_frame hc rd wr) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact free_below hL (by omega)

/-- Bytes of `scratch` at a call's entry. -/
theorem ce_scr (hL : L.Ok) (hst : 8 ≤ L.st) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) {o l : Nat}
    (h : o + l ≤ 65536) :
    bytesAt (t.callEntry.withRegions rd wr).mem (at' L.S o) l = bytesAt t.mem (at' L.S o) l :=
  bytesAt_frame (ce_frame hc rd wr) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [below_SP (by omega)]
    exact (hL.cs_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (hL.scr_sub h)) (by omega)

theorem adr_ce (hL : L.Ok) (hst : 8 ≤ L.st) {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) {a16 : List Byte}
    (ha : Adr L t.mem a16) : Adr L (t.callEntry.withRegions rd wr).mem a16 := fun k hk => by
  have hn := hL.n32
  rw [ce_scr hL hst hc rd wr (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega),
    ce_scr hL hst hc rd wr (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)]
  exact ha k hk

/-- What a call that writes `R`, a part of the signature, and at most
`changes` and its stack, leaves. -/
theorem after_call {p : Params} (hL : L.Ok) (hn : L.n = p.n) {k : Nat} (hk : k ≤ L.st) (hst : 8 ≤ L.st) {t : State}
    (hc : Ctx L g m₀ t) {rd wr : List Region} {R : Region} (hR : Region.Sub R L.SIG)
    {s' : State} (hrd : s'.rd = t.rd) (hwr : s'.wr = t.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = t.gpr r)
    (hf : Frame (changes p L.S ++ [R, below ((t.callEntry.withRegions rd wr).gpr .rsp) k])
      (t.callEntry.withRegions rd wr).mem s'.mem) :
    Ctx L g m₀ s' ∧ (∀ i < 4, s'.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64) ∧
      ∀ {a : Addr} {l : Nat}, Region.Sub ⟨a, l⟩ L.SIG → Region.Disjoint ⟨a, l⟩ R → l ≤ 2 ^ 64 →
        bytesAt s'.mem a l = bytesAt t.mem a l := by
  have hn32 := hL.n32
  have fr : Frame (below L.SP 8 :: (changes p L.S ++ [R, below ((t.callEntry.withRegions rd wr).gpr .rsp) k]))
      t.mem s'.mem :=
    ((ce_frame hc rd wr).mono fun r hr => by simp at hr; simp [hr]).trans (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
  have free : ∀ r ∈ below L.SP 8 :: (changes p L.S ++ [R, below ((t.callEntry.withRegions rd wr).gpr .rsp) k]),
      Free L r := by
    intro r hr
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr | rfl | rfl
    · exact free_below hL (by omega)
    · exact free_changes hL hn r hr
    · exact .inr (.inr hR)
    · exact .inr (.inl (stk_cs hk hc rd wr))
  have hb8 : Region.Sub (below L.SP 8) L.CS := by rw [below_SP (by omega)]; exact Offset.sub_base _ (by omega)
  refine ⟨hc.called hL hrd hwr hcs fr free, fun i hi => Thash4Avx.readW_frame fr fun r hr => ?_,
    fun {a l} hs hd hl => bytesAt_frame fr (fun r hr => ?_) hl⟩
  · have hv : Region.Sub ⟨L.var i, 8⟩ L.SCR := fun a h => hL.scr_sub (o := oKgSave + 48) (l := 32)
      (by rw [show oKgSave = 34080 from rfl]; omega) a (var_sub hL hi a h)
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr | rfl | rfl
    · exact (hL.cs_scr.sub_left hb8).symm.sub_left hv
    · exact ((changes_vars hn hn32 r hr).symm.sub_left (var_sub hL hi))
    · exact (hL.sSig.sub_right hR).sub_left hv
    · exact (hL.cs_scr.sub_left (stk_cs hk hc rd wr)).symm.sub_left hv
  · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr | rfl | rfl
    · exact (hL.cs_sig.sub_left hb8).symm.sub_left hs
    · have h2 : Region.Sub ⟨L.S, Layout.oSigTmp⟩ L.SCR :=
        Region.sub_prefix (by simp only [show Layout.oSigTmp = 31648 from rfl]; omega)
      exact (hL.sSig.symm.sub_left hs).sub_right fun x h => h2 x (Levels.changes_low (p := p) (by omega) L.S r hr x h)
    · exact hd
    · exact (hL.cs_sig.sub_left (stk_cs hk hc rd wr)).symm.sub_left hs

/-! ## `forsSign` -/

/-- A FORS signing function: code proven against `forsContract`, whose
calls take at most `stack` bytes. -/
structure ForsFn (p : Params) (c : Prog isa) where
  stack : Nat
  correct : ∀ s, (forsContract p stack).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (forsContract p stack).post s s'
  ct : ConstantTime isa (forsContract p stack).pre (forsContract p stack).pub c
  nosp : NoSp c
  depth : c.depth ≤ 8

theorem forsCall_ok {p : Params} {c : Prog isa} (F : ForsFn p c) (hFs : F.stack ≤ L.st) (hL : L.Ok)
    (hst : 8 ≤ L.st) (hn : L.n = p.n) (hsl : p.n + p.forsSigLen ≤ L.sigL) (hfl : p.n + p.forsSigLen < 2 ^ 31)
    (hmd : p.mdLen ≤ 64) {t : State} (hc : Ctx L g m₀ t) {a16 : List Byte} (ha : Adr L t.mem a16)
    {kp : Nat} (hkp : kp < 2 ^ 32) (h1 : t.gpr .rdi = L.S) (h2 : t.gpr .rsi = L.sig + BitVec.ofNat 64 p.n)
    (h3 : t.gpr .rdx = BitVec.ofNat 64 kp) (name : String) {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → (∀ i < 4, t'.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64) →
      bytesAt t'.mem (L.sig + BitVec.ofNat 64 p.n) p.forsSigLen =
        forsSign p (mdAt p t.mem L.S) (L.skSeed m₀) (L.pkSeed m₀) (Proof.SlhDsa.forsAdrs a16 kp) →
      bytesAt t'.mem (at' L.S Layout.oMsg) p.n =
        forsPkFromSig p (forsSign p (mdAt p t.mem L.S) (L.skSeed m₀) (L.pkSeed m₀) (Proof.SlhDsa.forsAdrs a16 kp))
          (mdAt p t.mem L.S) (L.pkSeed m₀) (Proof.SlhDsa.forsAdrs a16 kp) →
      (∀ {a : Addr} {l : Nat}, Region.Sub ⟨a, l⟩ L.SIG → Region.Disjoint ⟨a, l⟩ ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩ →
        l ≤ 2 ^ 64 → bytesAt t'.mem a l = bytesAt t.mem a l) →
      MxEq t t' → Q t') :
    WP isa (.call name c) t Q := by
  have hn32 := hL.n32
  let wr : List Region := [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]
  have e1 : (t.callEntry.withRegions [] wr).gpr .rdi = L.S := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h1]
  have e2 : (t.callEntry.withRegions [] wr).gpr .rsi = L.sig + BitVec.ofNat 64 p.n := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h2]
  have e3 : (t.callEntry.withRegions [] wr).gpr .rdx = BitVec.ofNat 64 kp := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h3]
  have e4 : (t.callEntry.withRegions [] wr).gpr .rsp = L.SP - 8 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hc.rsp]
  have hkp' : (BitVec.ofNat 64 kp).toNat = kp := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : Region.Sub ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩ L.SIG := Offset.sub_base _ hsl
  have hfit : (L.sig + BitVec.ofNat 64 p.n).toNat + p.forsSigLen ≤ 2 ^ 64 := by
    have := hL.nSig
    have h' : (L.sig + BitVec.ofNat 64 p.n).toNat ≤ L.sig.toNat + p.n := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
    omega
  have env := (ce_ctx hL hst hc [] wr).env hn (adr_ce hL hst hc [] wr ha)
  have sk := (ce_ctx hL hst hc [] wr).skAt hn
  have hpre : (forsContract p F.stack).pre (t.callEntry.withRegions [] wr) := by
    simp only [forsContract, e1, e3, hkp']
    exact ⟨by rw [e2]; exact regions_ok hL hFs hst hc hsub hfit, ⟨_, _, env⟩, hkp⟩
  obtain ⟨hcov, hcovw⟩ := covers_call (R := ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩) hc
    ⟨L.SIG, by simp, Offset.contains_base _ hsl (by omega)⟩
  have hd := F.depth
  refine WP.call_mx F.correct F.nosp (by omega) hpre hcov hcovw
    fun s' hrd hwr hcs _ _ ⟨s₂, hm₂, _, hpost⟩ hmx => ?_
  simp only [forsContract, e1, e2, e3, hkp'] at hpost
  obtain ⟨_, hsig, hmsg, hfr⟩ := hpost _ _ _ env sk
  rw [hm₂] at hsig hmsg hfr
  obtain ⟨hc', hv, hS⟩ := after_call hL hn hFs hst hc hsub hrd hwr hcs hfr
  have hmd' : mdAt p (t.callEntry.withRegions [] wr).mem L.S = mdAt p t.mem L.S :=
    ce_scr hL hst hc [] wr (by simp only [show Layout.oDigest = 30304 from rfl]; omega)
  rw [hmd'] at hsig hmsg
  exact k s' hc' hv hsig hmsg hS hmx

/-! ## `xmssTree` -/

theorem xmssCall_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hz : Wots4.Sz p) (hh : XmssTree.Hps p.hp) (hst : T.stack + 24 ≤ L.st) (hs62 : L.st < 2 ^ 62) (hL : L.Ok)
    (hn : L.n = p.n) {o : Nat} (hsl : o + p.xmssSigLen ≤ L.sigL) (ho : o + p.xmssSigLen < 2 ^ 31) {t : State}
    (hc : Ctx L g m₀ t) {a16 : List Byte} (ha : Adr L t.mem a16) {idx : Nat} (hidx : idx < 2 ^ p.hp)
    (h1 : t.gpr .rdi = L.S) (h2 : t.gpr .rsi = BitVec.ofNat 64 idx) (h3 : t.gpr .rdx = L.sig + BitVec.ofNat 64 o)
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → (∀ i < 4, t'.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64) →
      bytesAt t'.mem (at' L.S Layout.oMsg) p.n =
        xmssNode p (L.skSeed m₀) 0 p.hp (L.pkSeed m₀) (Proof.SlhDsa.treeAdrs a16) →
      bytesAt t'.mem (L.sig + BitVec.ofNat 64 o) p.xmssSigLen =
        xmssSign p (bytesAt t.mem (at' L.S Layout.oMsg) p.n) (L.skSeed m₀) idx (L.pkSeed m₀) (Proof.SlhDsa.treeAdrs a16) →
      (∀ {a : Addr} {l : Nat}, Region.Sub ⟨a, l⟩ L.SIG → Region.Disjoint ⟨a, l⟩ ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩ →
        l ≤ 2 ^ 64 → bytesAt t'.mem a l = bytesAt t.mem a l) →
      MxEq t t' → Q t') :
    WP isa (.call f.xmssName (Impl.SlhDsa.X86_64.Shake.xmssCode p f)) t Q := by
  have hn32 := hL.n32
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  have hidx' : idx < 2 ^ 64 := Nat.lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) (by omega))
  have hcode : Impl.SlhDsa.X86_64.Shake.xmssCode p f =
      Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp f.t4name f.wotsName f.levelsName T.code := by
    rw [Impl.SlhDsa.X86_64.Shake.xmssCode, ht]; rfl
  rw [hcode]
  let wr : List Region := [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩]
  have e1 : (t.callEntry.withRegions [] wr).gpr .rdi = L.S := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h1]
  have e2 : (t.callEntry.withRegions [] wr).gpr .rsi = BitVec.ofNat 64 idx := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h2]
  have e3 : (t.callEntry.withRegions [] wr).gpr .rdx = L.sig + BitVec.ofNat 64 o := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h3]
  have hidx'' : (BitVec.ofNat 64 idx).toNat = idx := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx']
  have hsub : Region.Sub ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩ L.SIG := Offset.sub_base _ hsl
  have hfit : (L.sig + BitVec.ofNat 64 o).toNat + p.xmssSigLen ≤ 2 ^ 64 := by
    have := hL.nSig
    have h' : (L.sig + BitVec.ofNat 64 o).toNat ≤ L.sig.toNat + o := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
    omega
  have env := (ce_ctx hL (by omega) hc [] wr).env hn (adr_ce hL (by omega) hc [] wr ha)
  have sk := (ce_ctx hL (by omega) hc [] wr).skAt hn
  have hpre : (xmssContract p L.st).pre (t.callEntry.withRegions [] wr) := by
    simp only [xmssContract, e1, e2, hidx'']
    exact ⟨by rw [e3]; exact regions_ok hL (Nat.le_refl _) (by omega) hc hsub hfit, ⟨_, _, env⟩,
      Nat.lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) (by omega))⟩
  obtain ⟨hcov, hcovw⟩ := covers_call (R := ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩) hc
    ⟨L.SIG, by simp, Offset.contains_base _ hsl (by omega)⟩
  refine XmssTree.xmsscall_ok hz T f.t4name f.wotsName f.levelsName f.xmssName hst (by omega) hhp hhp9 hpre hcov
    hcovw fun s' hrd hwr hcs _ ⟨s₂, hm₂, _, hpost⟩ hmx => ?_
  simp only [xmssContract, e1, e2, e3, hidx''] at hpost
  obtain ⟨_, hroot, hsig, hfr⟩ := hpost _ _ _ env sk
  rw [hm₂] at hroot hsig hfr
  obtain ⟨hc', hv, hS⟩ := after_call hL hn (Nat.le_refl _) (by omega) hc hsub hrd hwr hcs hfr
  have hM : bytesAt (t.callEntry.withRegions [] wr).mem (at' L.S Layout.oMsg) p.n = bytesAt t.mem (at' L.S Layout.oMsg) p.n :=
    ce_scr hL (by omega) hc [] wr (by simp only [show Layout.oMsg = 30496 from rfl]; omega)
  rw [hM] at hsig
  exact k s' hc' hv hroot (hsig hidx) hS hmx

/-! ## The lanes' addresses -/

theorem lanesR_scr {L : SL} (hL : L.Ok) : Region.Sub (KeyGen.lanesR L.S) L.SCR := hL.scr_sub (by
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
    (keepF 8 (by omega)).trans hc.pScr, (keepF 16 (by omega)).trans hc.pRnd, (keepF 24 (by omega)).trans hc.pSig,
    (keepF 32 (by omega)).trans hc.pCtxLen, (keepF 40 (by omega)).trans hc.pCtx, (keepF 48 (by omega)).trans hc.pLen,
    (keepF 56 (by omega)).trans hc.pMsg, (keepF 64 (by omega)).trans hc.pKey, ?_,
    hc.frame.trans (Frame.sub hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨L.SCR, by simp, lanesR_scr hL⟩),
    fun r hr k hk => ?_, fun c hc' => ?_, fun k hk => (hsA k hk).trans (hc.seedA k hk), fun k hk => (hsB k hk).trans (hc.seedB k hk)⟩
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
  · rw [bytesAt_frame hf (dl (o := Layout.oKeys + 32 * c) (by simp only [Layout.oKeys]; omega)
      (by simp only [Layout.oKeys]; omega)) (by omega)]
    exact hc.keys c hc'

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

end VG.Proof.SlhDsa.X86_64.SignTop
