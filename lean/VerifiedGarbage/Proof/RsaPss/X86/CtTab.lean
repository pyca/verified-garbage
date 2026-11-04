module

public import VerifiedGarbage.Proof.RsaPss.X86.TabCall
public import VerifiedGarbage.Proof.RsaPss.X86.CtHash
public import VerifiedGarbage.Proof.RsaPss.X86.CtComp
public import VerifiedGarbage.Proof.MdHashTable.X86
meta import VerifiedGarbage.Proof.RsaPss.X86.TabCall
meta import VerifiedGarbage.Proof.RsaPss.X86.CtHash
meta import VerifiedGarbage.Proof.RsaPss.X86.CtComp
meta import VerifiedGarbage.Proof.MdHashTable.X86
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: hashing through the table of `MdHash`, the calls

The table at `p` (`HFacts`): in the run from `σ`, its words 0, 3 and 4 hold
the addresses `ai`, `ac` and `ad` of `h`'s streaming `init`, compression
function and digest (`dn`), which an indirect call of `f`'s functions to
them reaches. With the table's address in `sTab`, each call through it is the
call of `h`'s function (`tcallP_vp`): `init` (`initT_vp`), one compression
(`cmpT_vp`) and the digest (`outT_vp`), as `init_vp`, `comp_vp` and
`out_vp` are for the direct calls. Every stage keeps the addresses of the
statics (`VP.syms`), which the indirect calls need.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaOaep.X86 (tcall sTab)
open VG.Proof.RsaOaep.X86 (VP.syms)
open VG.Proof.Pbkdf2.Stream.X86 (InitArgs After init_frame init_rel stk)
open VG.Proof.Pbkdf2.Md.X86 (CmpArgs cmp_frame cmpFrame_rel)
open VG.Proof.MdHashTable.X86 (DigArgs dig_frame dig_rel)

/-- What hashing needs of its table at `p` in the run from `σ`. -/
structure HFacts (h : PssHash) (dn : String) (f : MdFns) (p ai ac ad : BitVec 32) (σ : State) : Prop where
  fi : f.init.find? (fun q => (σ.syms q.1).setWidth 64 == (σ.syms h.H.st.initN).setWidth 64) =
    some (h.H.st.initN, h.H.st.initC)
  fc : f.comp.find? (fun q => (σ.syms q.1).setWidth 64 == (σ.syms h.H.compN).setWidth 64) = some (h.H.compN, h.H.compC)
  fd : f.dig.find? (fun q => (σ.syms q.1).setWidth 64 == (σ.syms dn).setWidth 64) =
    some (dn, Impl.MdHashTable.X86.digest h.H.out)
  m0 : σ.mem.readW (VG.X86.addr p (4 * 0)) 32 = ai
  m3 : σ.mem.readW (VG.X86.addr p (4 * 3)) 32 = ac
  m4 : σ.mem.readW (VG.X86.addr p (4 * 4)) 32 = ad
  ai : σ.syms h.H.st.initN = ai
  ac : σ.syms h.H.compN = ac
  ad : σ.syms dn = ad

/-- What the calls through the table need of the digest's code, which the
kernel checks of each hash function. -/
structure DigCerts (h : PssHash) : Prop where
  sp : NoSp (Impl.MdHashTable.X86.digest h.H.out)
  ct : ∃ hc, (VG.Taint.check VG.X86.taint (τr [.esp, .ebx, .eax]) (Impl.MdHashTable.X86.digest h.H.out) hc).isSome
    = true

theorem outSet_taint : TaintOk [.esp, .ebp] (.block outSet) := ⟨_, by taint_decide⟩
theorem mov1_taint : TaintOk [.esp, .ebp] (.block [.mov .ecx (.imm 1)]) := ⟨_, by taint_decide⟩

variable {L : Lay} {scr : BitVec 32} (h : PssHash) {dn : String} {f : MdFns} {p ai ac ad : BitVec 32}

/-- The table's address and its words, from what a stage keeps. -/
structure TabAt (L : Lay) (h : PssHash) (dn : String) (f : MdFns) (p ai ac ad : BitVec 32)
    (Inv : State → Mem → Prop) : Prop where
  tab : ∀ σ m, Inv σ m → HFacts h dn f p ai ac ad σ
  slot : ∀ σ m, Inv σ m → m.readW (L.fr sTab) 32 = p
  tbl : ∀ k, k < 5 → ∃ R ∈ L.ro, R.Contains (VG.X86.addr p (4 * k)) 4
  ne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []

/-- The streaming `init`, through the table, on the hash value at `oSt`. -/
theorem initT_vp (hg : Geo L scr) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt (h.N + h.B), L.LOW] m m' → Inv σ m')
    (hT : TabAt L h dn f p ai ac ad Inv) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem) ∧ s.syms = σ.syms) (initPartT f)
      (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ h.md.stateAt s.mem (sa scr oSt) = h.ok.iv) ∧ s.syms = σ.syms) := by
  have hN := h.N_le
  have hBl := h.B_le
  have fit := hg.fit
  have hS := h.S_eq
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .ebx = scr + BitVec.ofNat 32 oSt) ∧
      s.syms = σ.syms)
    (VP.syms (VP.taint [.esp, .ebp] initArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi⟩ => ?_)) ?_
  · refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => WP.block_nil ⟨(hc.upd u1 (by decide) (by decide)).upd u2
      (by decide) (by decide), by rw [u2.mem, u1.mem]; exact hi, by rw [u2.gpr, u1.gpr, hc.ebp]⟩
  have fitS : (scr + BitVec.ofNat 32 oSt).toNat + h.H.S ≤ 2 ^ 32 := by
    rw [hg.scr_lt (by decide), hS]; unfold oSt oRsa at *; omega
  have hsub : Region.Sub ⟨(scr + BitVec.ofNat 32 oSt).setWidth 64, h.H.S⟩ (sR scr oSt (h.N + h.B)) := by
    rw [hg.scrA (by decide), hS]; exact fun _ h => h
  have args : ∀ σ s, Ctx L scr σ s → s.gpr .ebx = scr + BitVec.ofNat 32 oSt →
      InitArgs (H := h.H.st) s .ebx (scr + BitVec.ofNat 32 oSt) := fun σ s hc bx => by
    refine ⟨bx, by decide, ?_, ?_, ?_, fitS⟩
    · rw [hc.st.sp]; have := hc.st.ok.BC; have := hg.C48; omega
    · rw [hg.scrA (by decide), show h.H.st.S = h.N + h.B from hS]
      exact Covers.one (hg.wr hc.st (by unfold oSt oRsa; omega))
    · exact (((hg.low hc.st.ok (o := oSt) (n := h.N + h.B) (by unfold oSt oRsa; omega)).symm.sub_left
        (stk_low hg hc)).sub_right hsub)
  refine tcallP_vp hg (k := 0) (by decide) hT.ne.1 (fun _ _ h => h.1.1)
    (fun σ s t v ⟨⟨hc, hi, bx⟩, sy⟩ u => ⟨⟨hc.upd u (by decide) (by decide), u.mem ▸ hi,
      (u.other _ (by decide)).trans bx⟩, u.syms.trans sy⟩) (fun _ _ h => h.2)
    (fun σ s h => hT.slot σ _ h.1.2.1) (hT.tbl 0 (by decide))
    (fun σ s h => let T := hT.tab σ _ h.1.2.1; ⟨T.m0, T.ai, T.fi⟩) (VP.syms ?_)
  refine VP.of_ct (fun _ _ => init_rel h.ok.hH (sp := L.B) fun a b hab =>
    ⟨args _ _ hab.1.1 hab.1.2.2, args _ _ hab.2.1 hab.2.2.2, hab.1.1.st.sp, hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hi, bx⟩
  refine init_frame h.ok.hH (args σ s hc bx) fun s' af rp => ?_
  have fr : Frame [sR scr oSt (h.N + h.B), L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, hsub⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, stk_low hg hc⟩
  refine ⟨hc.write fr (fun r hr => ?_) af.rd af.wr af.esp (af.cs .ebp (by simp [calleeSaved])), hI σ _ _ hi fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hg.inW (by unfold oSt oRsa; omega)
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩
  · rw [hg.scrA (by decide)] at rp
    obtain ⟨e, -⟩ := h.ok.link.repr _ _ _ rp
    rw [e, List.length_nil, Nat.zero_div, MdStream.Md.compressList_zero]

/-- One compression, through the table, of the block at `oSt + N` into the
hash value at `oSt`. -/
theorem cmpT_vp (hg : Geo L scr) {X : State → Mem → Prop} (hT : TabAt L h dn f p ai ac ad X) :
    VP (fun σ s => (Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .ebx = scr + BitVec.ofNat 32 oSt ∧
        s.gpr .eax = scr + BitVec.ofNat 32 (oSt + h.N)) ∧ s.syms = σ.syms)
      (cmpT f)
      (fun σ s => (Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame (compW h L scr) m₀ s.mem ∧
        h.md.stateAt s.mem (sa scr oSt) =
          h.md.compress (h.md.stateAt m₀ (sa scr oSt)) (h.md.blockAt m₀ (sa scr (oSt + h.N)))) ∧
        s.syms = σ.syms) := by
  have hN := h.N_le
  have hso := h.so_le
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hB0 : 0 < h.B := by omega
  have fit := hg.fit
  unfold oRsa at fit
  have a0 : sa scr oCW = scr.setWidth 64 := by simp [sa, oCW]
  have aSt : (scr + BitVec.ofNat 32 oSt).setWidth 64 = sa scr oSt := hg.scrA (by decide)
  have args : ∀ σ s, Ctx L scr σ s → s.gpr .ebx = scr + BitVec.ofNat 32 oSt →
      s.gpr .eax = scr + BitVec.ofNat 32 (oSt + h.N) →
      CmpArgs h.N h.B h.H.so s (scr + BitVec.ofNat 32 oSt) scr := fun σ s hc bx ax => by
    refine ⟨bx, by rw [ax, BitVec.add_assoc, BitVec.ofNat_add_ofNat], hc.ebp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc.st.sp]; have := hc.st.ok.BC; have := hg.C48; omega
    · rw [aSt]; exact Covers.one (hg.wr hc.st (by pomega))
    · rw [← a0]; exact Covers.one (hg.wr hc.st (by pomega))
    · rw [aSt, ← a0]; exact Geo.sep (by pomega) (by pomega) (by pomega)
    · rw [aSt]; exact (hg.low hc.st.ok (by pomega)).symm.sub_left (stk_low hg hc)
    · rw [← a0]; exact (hg.low hc.st.ok (by pomega)).symm.sub_left (stk_low hg hc)
    · rw [hg.scr_lt (by decide)]; pomega
    · pomega
  -- `ecx := 1`.
  refine VP.seq (G := fun σ s => ((Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .ebx = scr + BitVec.ofNat 32 oSt ∧
      s.gpr .eax = scr + BitVec.ofNat 32 (oSt + h.N)) ∧ s.gpr .ecx = 1) ∧ s.syms = σ.syms)
    (VP.syms (VP.taint [.esp, .ebp] mov1_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hx, bx, ax⟩ => ?_)) ?_
  · refine wp_movi fun t1 u1 => WP.block_nil ⟨⟨hc.upd u1 (by decide) (by decide), u1.mem ▸ hx,
      (u1.other _ (by decide)).trans bx, (u1.other _ (by decide)).trans ax⟩, u1.gpr⟩
  refine tcallP_vp hg (k := 3) (by decide) hT.ne.2.1 (fun _ _ h => h.1.1.1)
    (fun σ s t v ⟨⟨⟨hc, hx, bx, ax⟩, cx⟩, sy⟩ u => ⟨⟨⟨hc.upd u (by decide) (by decide), u.mem ▸ hx,
      (u.other _ (by decide)).trans bx, (u.other _ (by decide)).trans ax⟩, (u.other _ (by decide)).trans cx⟩,
      u.syms.trans sy⟩) (fun _ _ h => h.2)
    (fun σ s h => hT.slot σ _ h.1.1.2.1) (hT.tbl 3 (by decide))
    (fun σ s h => let T := hT.tab σ _ h.1.1.2.1; ⟨T.m3, T.ac, T.fc⟩) (VP.syms ?_)
  refine VP.of_ct (fun _ _ => cmpFrame_rel h.ok.comp hB0 (sp := L.B) fun a b hab =>
    ⟨⟨args _ _ hab.1.1.1 hab.1.1.2.2.1 hab.1.1.2.2.2, hab.1.2⟩, ⟨args _ _ hab.2.1.1 hab.2.1.2.2.1 hab.2.1.2.2.2, hab.2.2⟩,
      hab.1.1.1.st.sp, hab.2.1.1.st.sp⟩) ?_
  rintro σ s ⟨⟨hc, hx, bx, ax⟩, cx⟩
  refine cmp_frame h.ok.comp hB0 (args σ s hc bx ax) cx fun s' af e => ?_
  have fr : Frame (compW h L scr) s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aSt]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [← a0]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), stk_low hg hc⟩
  refine ⟨hc.write fr (fun r hr => ?_) af.rd af.wr af.esp (af.cs .ebp (by simp [calleeSaved])), s.mem, hx, fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hg.inW (by pomega)
    · exact hg.inW (by pomega)
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩
  rw [aSt, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa] at e
  exact e

/-- The digest, through the table, of the hash value at `oSel`, to `oDig`. -/
theorem outT_vp (hg : Geo L scr) (hd : DigCerts h) {X : State → Mem → Prop} (hT : TabAt L h dn f p ai ac ad X) :
    VP (fun σ s => (Ctx L scr σ s ∧ X σ s.mem) ∧ s.syms = σ.syms) (outPartT f)
      (fun σ s => (Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr oDig h.N, L.LOW] m₀ s.mem ∧
        ∀ i < h.N, s.mem (sa scr (oDig + i)) = (h.md.digest (h.md.stateAt m₀ (sa scr oSel))).getD i 0) ∧
        s.syms = σ.syms) := by
  have hN := h.N_le
  have fit := hg.fit
  unfold oRsa at fit
  have aB : (scr + BitVec.ofNat 32 oSel).setWidth 64 = sa scr oSel := hg.scrA (by decide)
  have aA : (scr + BitVec.ofNat 32 oDig).setWidth 64 = sa scr oDig := hg.scrA (by decide)
  have args : ∀ σ s, Ctx L scr σ s → s.gpr .ebx = scr + BitVec.ofNat 32 oSel →
      s.gpr .eax = scr + BitVec.ofNat 32 oDig →
      DigArgs h.N s (scr + BitVec.ofNat 32 oSel) (scr + BitVec.ofNat 32 oDig) := fun σ s hc bx ax => by
    refine ⟨bx, ax, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc.st.sp]; have := hc.st.ok.BC; have := hg.C48; omega
    · rw [aB]; exact Covers.one (hg.rd hc.st (by pomega))
    · rw [aA]; exact Covers.one (hg.wr hc.st (by pomega))
    · rw [aB, aA]; exact Geo.sep (by pomega) (by pomega) (by pomega)
    · rw [aB]; exact (hg.low hc.st.ok (by pomega)).symm.sub_left (stk_low hg hc)
    · rw [aA]; exact (hg.low hc.st.ok (by pomega)).symm.sub_left (stk_low hg hc)
    · rw [hg.scr_lt (by decide)]; pomega
    · rw [hg.scr_lt (by decide)]; pomega
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .ebx = scr + BitVec.ofNat 32 oSel ∧
      s.gpr .eax = scr + BitVec.ofNat 32 oDig) ∧ s.syms = σ.syms)
    (VP.syms (VP.taint [.esp, .ebp] outSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hx⟩ => ?_)) ?_
  · simp only [outSet, atS, addi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 => WP.block_nil ?_
    have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨(((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide)
      (by decide)).upd u4 (by decide) (by decide), by rw [m4]; exact hx, ?_, ?_⟩
    · simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · simp (disch := decide) only [u4.gpr, u3.gpr, u2.other, u1.other, hc.ebp]
  refine tcallP_vp hg (k := 4) (by decide) hT.ne.2.2 (fun _ _ h => h.1.1)
    (fun σ s t v ⟨⟨hc, hx, bx, ax⟩, sy⟩ u => ⟨⟨hc.upd u (by decide) (by decide), u.mem ▸ hx,
      (u.other _ (by decide)).trans bx, (u.other _ (by decide)).trans ax⟩, u.syms.trans sy⟩) (fun _ _ h => h.2)
    (fun σ s h => hT.slot σ _ h.1.2.1) (hT.tbl 4 (by decide))
    (fun σ s h => let T := hT.tab σ _ h.1.2.1; ⟨T.m4, T.ad, T.fd⟩) (VP.syms ?_)
  refine VP.of_ct (fun _ _ => dig_rel (H := h.md) h.ok.out hd.ct (sp := L.B) fun a b hab =>
    ⟨args _ _ hab.1.1 hab.1.2.2.1 hab.1.2.2.2, args _ _ hab.2.1 hab.2.2.2.1 hab.2.2.2.2, hab.1.1.st.sp,
      hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hx, bx, ax⟩
  refine dig_frame (H := h.md) h.ok.out hd.sp (args σ s hc bx ax) fun s' af e => ?_
  have fr : Frame [sR scr oDig h.N, L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aA]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, stk_low hg hc⟩
  refine ⟨hc.write fr (fun r hr => ?_) af.rd af.wr af.esp (af.cs .ebp (by simp [calleeSaved])), s.mem, hx, fr,
    fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hg.inW (by pomega)
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩
  · have := e i hi
    rw [aA, aB] at this
    rw [show sa scr (oDig + i) = sa scr oDig + BitVec.ofNat 64 i by
      rw [sa, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact this

end VG.Proof.RsaPss.X86
