module

public import VerifiedGarbage.Proof.RsaPss.X86.TabCall
public import VerifiedGarbage.Proof.RsaPss.X86.CtHash
public import VerifiedGarbage.Proof.RsaPss.X86.CtComp
public import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtSel
import VerifiedGarbage.Proof.RsaPss.X86.CtPad
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
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

theorem TabAt.mono {Inv X : State → Mem → Prop} (h' : TabAt L h dn f p ai ac ad Inv) (hX : ∀ σ m, X σ m → Inv σ m) :
    TabAt L h dn f p ai ac ad X :=
  ⟨fun σ m hx => h'.tab σ m (hX σ m hx), fun σ m hx => h'.slot σ m (hX σ m hx), h'.tbl, h'.ne⟩

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

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)
open VG.Impl.RsaOaep.X86 (sTab)
open VG.Proof.RsaOaep.X86 (VP.syms)

variable {L : Lay} {scr : BitVec 32} (h : PssHash) {dn : String} {f : MdFns} {p ai ac ad : BitVec 32}

/-- The compression loop, through the table. -/
theorem compLoopT_vp (hg : Geo L scr) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {yv : State → Nat → Byte} {lb : State → Nat} (hlb : ∀ σ, lb σ < nbm)
    {Inv : State → Mem → Prop} (hI : ∀ σ m m', Inv σ m → Frame (loopW h L scr) m m' → Inv σ m')
    (hslb : ∀ σ m, Inv σ m → m.readW (L.fr sLb) 32 = BitVec.ofNat 32 (lb σ))
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm) (hTab : TabAt L h dn f p ai ac ad Inv) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ (∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = yv σ i) ∧
        h.md.stateAt s.mem (sa scr oSt) = h.ok.iv) ∧ s.syms = σ.syms)
      (compLoopT f h.H)
      (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ h.md.stateAt s.mem (sa scr oSel) =
        h.md.compressList h.ok.iv (ylist (yv σ) (nbm * h.B)) (lb σ + 1)) ∧ s.syms = σ.syms) := by
  have _ : oCW = 0 := rfl
  have _ : oSt = 512 := rfl
  have _ : oSel = 768 := rfl
  have _ : oDig = 832 := rfl
  have _ : oLen = 896 := rfl
  have _ : oEm = 1024 := rfl
  have _ : oY = 2048 := rfl
  have _ : oRsa = 8192 := rfl
  have _ : frameBytes = 144 := rfl

  have hN := h.N_le
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hso := h.so_le
  have fit := hg.fit
  unfold oRsa at fit
  obtain ⟨σ', ok⟩ := hg.ok
  have hC : L.C ≤ 2 ^ 32 := by have := ok.BC; have := L.B.isLt; omega_arith
  have nbB : nbm ≤ nbm * h.B := Nat.le_mul_of_pos_right nbm (by omega_arith)
  generalize hT : nbm * h.B = T at hnb nbB ⊢
  -- What the pieces write, against what they keep.
  have sl : ∀ d, d + 4 ≤ frameBytes → ∀ {o n : Nat}, o + n ≤ oRsa → (slotR L d).Disjoint (sR scr o n) :=
    fun d hd o n h => hg.slot ok h (by rw [hg.F]; omega_arith)
  have slow : ∀ d, d + 4 ≤ frameBytes → (slotR L d).Disjoint L.LOW := fun d hd => Lay.fr_low (by omega_arith) hC
  have inL : ∀ r ∈ [sR scr oSel h.N], ∃ R ∈ loopW h L scr, Region.Sub r R := by
    simp only [List.mem_singleton]; rintro r rfl; exact ⟨sR scr oSel h.N, by simp [loopW], fun _ h => h⟩
  have inB : ∀ r ∈ [slotR L sBi], ∃ R ∈ loopW h L scr, Region.Sub r R := by
    simp only [List.mem_singleton]; rintro r rfl; exact ⟨slotR L sBi, by simp [loopW], fun _ h => h⟩
  have wB : ∀ r ∈ [slotR L sBi], ∃ R ∈ L.W, Region.Sub r R := by
    simp only [List.mem_singleton]; rintro r rfl
    exact ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; decide)⟩
  let CS : Nat → State → State → Prop := fun b σ s =>
    Ctx L scr σ s ∧ Inv σ s.mem ∧ CM h L scr T (yv σ) (lb σ) b s.mem
  -- The first block.
  refine VP.seq (G := fun σ s => CS 0 σ s ∧ s.syms = σ.syms) (VP.syms (VP.taint [.esp, .ebp] compInit_taint
    (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, hy, hst⟩ => ?_)) ?_
  · simp only [compInit, mi, st]
    refine wp_movi fun t1 u1 => (hc.upd u1 (by decide) (by decide)).wp_st hg (by decide) fun t2 c2 u2 =>
      WP.block_nil ?_
    have fr : Frame [slotR L sBi] s.mem t2.mem := by rw [u2.mem, u1.mem]; exact slot_frame L _ _ _
    refine ⟨c2, hI σ _ _ hi (fr.sub inB), sbytes_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (sl sBi (by decide) (by omega_arith)).symm) (by omega_arith) hy,
      by rw [u2.mem, Mem.readW_writeW_self32, u1.gpr], ?_, fun h0 => absurd h0 (Nat.not_lt_zero _)⟩
    rw [stateAt_keep h fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (sl sBi (by decide) (by omega_arith)).symm),
      hst, Md.compressList_zero]
  -- The loop.
  refine (VP.loop (I := fun n σ s => (n ≤ nbm ∧ CS (nbm - n) σ s) ∧ s.syms = σ.syms) (fun n => ?_) (nbm - 1)).mono
    (fun σ s hs => ⟨⟨by omega_arith, by rw [show nbm - (nbm - 1 + 1) = 0 by omega_arith]; exact hs.1⟩, hs.2⟩)
    fun _ _ h => h
  by_cases hn : n + 1 ≤ nbm
  swap
  · exact VP.empty fun σ s ⟨⟨h, _⟩, _⟩ => hn h
  generalize hb : nbm - (n + 1) = b
  have hbn : b < nbm := by omega_arith
  have hbB : b * h.B + h.B ≤ T := by rw [← hT, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_arith)
  -- What each stage keeps of memory.
  let X1 : State → Mem → Prop := fun σ m => Inv σ m ∧ CM h L scr T (yv σ) (lb σ) b m
  let X3 : State → Mem → Prop := fun σ m => Inv σ m ∧ (∀ i < T, m (sa scr (oY + i)) = yv σ i) ∧
    m.readW (L.fr sBi) 32 = BitVec.ofNat 32 b ∧
    h.md.stateAt m (sa scr oSt) = h.md.compressList h.ok.iv (ylist (yv σ) T) (b + 1) ∧
    (lb σ < b → h.md.stateAt m (sa scr oSel) = h.md.compressList h.ok.iv (ylist (yv σ) T) (lb σ + 1))
  let X4 : State → Mem → Prop := fun σ m => Inv σ m ∧ (∀ i < T, m (sa scr (oY + i)) = yv σ i) ∧
    m.readW (L.fr sBi) 32 = BitVec.ofNat 32 b ∧
    h.md.stateAt m (sa scr oSt) = h.md.compressList h.ok.iv (ylist (yv σ) T) (b + 1) ∧
    (lb σ < b + 1 → h.md.stateAt m (sa scr oSel) = h.md.compressList h.ok.iv (ylist (yv σ) T) (lb σ + 1))
  have aD : (scr + BitVec.ofNat 32 (oSt + h.N)).setWidth 64 = sa scr (oSt + h.N) := hg.scrA (by omega_arith)
  have aS : (scr + BitVec.ofNat 32 (oY + b * h.B)).setWidth 64 = sa scr (oY + b * h.B) := hg.scrA (by omega_arith)
  show VP _ (.seq (.block (blkSet h.H)) (.seq Impl.Bignum.X86.copyBytes (.seq (.block (cmpSet h.H))
    (.seq (cmpT f) (.seq (.block (selSet h.H)) (.seq (countLoop selBody) (.block compNext))))))) _
  refine VP.seq (G := fun σ s => (CS b σ s ∧ s.gpr .esi = scr + BitVec.ofNat 32 (oY + b * h.B) ∧
      s.gpr .ebx = scr + BitVec.ofNat 32 (oSt + h.N) ∧ s.gpr .ecx = BitVec.ofNat 32 h.B) ∧ s.syms = σ.syms) (VP.syms ?_)
    (VP.seq (G := fun σ s => (Ctx L scr σ s ∧ X1 σ s.mem ∧
        ∀ i < h.B, s.mem (sa scr (oSt + h.N + i)) = yv σ (b * h.B + i)) ∧ s.syms = σ.syms) (VP.syms ?_)
    (VP.seq (G := fun σ s => ((Ctx L scr σ s ∧ X1 σ s.mem ∧
        ∀ i < h.B, s.mem (sa scr (oSt + h.N + i)) = yv σ (b * h.B + i)) ∧
        s.gpr .ebx = scr + BitVec.ofNat 32 oSt ∧ s.gpr .eax = scr + BitVec.ofNat 32 (oSt + h.N)) ∧ s.syms = σ.syms)
      (VP.syms ?_)
    (VP.seq (G := fun σ s => (Ctx L scr σ s ∧ X3 σ s.mem) ∧ s.syms = σ.syms) ?_
    (VP.seq (G := fun σ s => ((Ctx L scr σ s ∧ X3 σ s.mem) ∧ s.gpr .esi = scr + BitVec.ofNat 32 oSt ∧
        s.gpr .edi = scr + BitVec.ofNat 32 oSel ∧ s.gpr .ecx = BitVec.ofNat 32 h.N ∧
        s.gpr .edx = maskOf (b = lb σ)) ∧ s.syms = σ.syms) (VP.syms ?_)
    (VP.seq (G := fun σ s => (Ctx L scr σ s ∧ X4 σ s.mem) ∧ s.syms = σ.syms) (VP.syms ?_) ?_)))))
  · -- The block's address, and where it goes.
    refine (VP.taint [.esp, .ebp] h.certs.blkSet (sp_bp fun _ _ h => h.2.1) fun σ s ⟨hn', hc, hi, hm⟩ => ?_)
    simp only [blkSet, atS, ld, mi, addi, List.cons_append, List.nil_append, List.append_assoc]
    refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
    refine wp_shl (lgB h.H) (n := b) (by rw [h.pow_lg]; omega_arith) (by rw [u1.gpr, hm.bi]) fun t2 u2 => ?_
    refine wp_add fun t3 u3 _ => wp_addi fun t4 u4 => wp_mov fun t5 u5 => wp_addi fun t6 u6 =>
      wp_movi fun t7 u7 => WP.block_nil ?_
    have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨(((((c1.upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)).upd u4 (by decide)
      (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide),
      by rw [m7]; exact hi, by rw [m7]; exact hm⟩, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.gpr, u3.gpr, u2.gpr, u2.other, u1.other,
        hc.ebp, h.pow_lg]
      rw [BitVec.add_comm _ scr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm (b * h.B)]
    · simp (disch := decide) only [u7.other, u6.gpr, u5.gpr, u4.other, u3.other, u2.other, u1.other, hc.ebp]
    · rw [u7.gpr]
  · -- The block copied after the hash value.
    refine (copy_vp (hg.wbuf (o := oSt + h.N) (n := h.B) (by omega_arith) (by omega_arith))
      (hg.rbuf (o := oY + b * h.B) (n := h.B) (by omega_arith) (by omega_arith))
      (by rw [aS, aD]; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith) (Inv := X1)
      (f := fun σ i => yv σ (b * h.B + i)) ?_).mono
      (fun σ s ⟨⟨hc, hi, hm⟩, si, bx, cx⟩ => ⟨hc, ⟨hi, hm⟩, bx, si, cx, fun i hi' => ?_⟩)
      fun σ s ⟨hc, hx, hb'⟩ => ⟨hc, hx, fun i hi' => ?_⟩
    · intro σ m m' ⟨hi, hm⟩ fr
      rw [aD] at fr
      have one : ∀ {P : Region → Prop}, P (sR scr (oSt + h.N) h.B) → ∀ r ∈ [sR scr (oSt + h.N) h.B], P r := by
        intro P hP r hr; simp only [List.mem_singleton] at hr; subst hr; exact hP
      exact ⟨hI σ _ _ hi (fr.sub (one ⟨sR scr oSt (h.N + h.B), by simp [loopW], Offset.sub _ (by omega_arith) (by omega_arith)⟩)),
        hm.keep h fr (by omega_arith) (one (Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)))
          (one (sl sBi (by decide) (by omega_arith))) (one (Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)))
          (one (Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)))⟩
    · rw [hg.byteAt_scr (by omega_arith), Nat.add_assoc]; exact hm.y _ (by omega_arith)
    · rw [← hg.byteAt_scr (by omega_arith)]; exact hb' i hi'
  · -- The compression's registers.
    refine VP.taint [.esp, .ebp] h.certs.cmpSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hx, hblk⟩ => ?_
    simp only [cmpSet, atS, addi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 => WP.block_nil ?_
    have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨(((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide)
      (by decide)).upd u4 (by decide) (by decide), by rw [m4]; exact hx, by rw [m4]; exact hblk⟩, ?_, ?_⟩
    · simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · simp (disch := decide) only [u4.gpr, u3.gpr, u2.other, u1.other, hc.ebp]
  · -- The compression.
    refine (cmpT_vp h hg (X := fun σ m => X1 σ m ∧
        ∀ i < h.B, m (sa scr (oSt + h.N + i)) = yv σ (b * h.B + i)) (TabAt.mono h hTab fun _ _ hx => hx.1.1)).mono
      (fun σ s ⟨⟨⟨hc, hx, hblk⟩, bx, ax⟩, sy⟩ => ⟨⟨hc, ⟨hx, hblk⟩, bx, ax⟩, sy⟩)
      fun σ s ⟨⟨hc, m₀, ⟨⟨hi, hm⟩, hblk⟩, fr, e⟩, sy⟩ =>
        ⟨⟨hc, hI σ _ _ hi (fr.sub fun r hr => ?_), ?_, ?_, ?_, ?_⟩, sy⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sR scr oSt (h.N + h.B), by simp [loopW], Offset.sub _ (by omega_arith) (by omega_arith)⟩
      · exact ⟨sR scr oCW h.H.so, by simp [loopW], fun _ h => h⟩
      · exact ⟨L.LOW, by simp [loopW], fun _ h => h⟩
    · refine sbytes_keep fr (fun r hr => ?_) (by omega_arith) hm.y
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
      · exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
      · exact hg.low ok (by omega_arith)
    · refine slot_keep fr (fun r hr => ?_) hm.bi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sl sBi (by decide) (by omega_arith)
      · exact sl sBi (by decide) (by omega_arith)
      · exact slow sBi (by decide)
    · rw [e, hm.st, Md.compressList_succ]
      refine congrArg _ (h.md.parse_congr fun k hk => ?_)
      rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa, hblk k hk,
        ylist_getD (by have := Nat.mul_comm b h.B; omega_arith), Nat.mul_comm]
    · intro hl
      rw [stateAt_keep h fr (fun r hr => ?_), hm.sel hl]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
      · exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
      · exact hg.low ok (by omega_arith)
  · -- The selection's registers.
    refine VP.taint [.esp, .ebp] h.certs.selSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hx⟩ => ?_
    simp only [selSet, atS, ld, mi, addi, isZero, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 => ?_
    have c4 : Ctx L scr σ t4 := (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3
      (by decide) (by decide)).upd u4 (by decide) (by decide)
    refine c4.wp_slot hg (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
    refine wp_xorm (B := L.B) (by rw [c5.st.sp]) (by rw [hg.aFr ok sLb (by decide)]; exact c5.rFr hg sLb (by decide))
      fun t6 u6 => ?_
    refine wp_subi fun t7 u7 c7 _ => wp_sbb_self c7 fun t8 u8 => wp_movi fun t9 u9 => WP.block_nil ?_
    have m9 : t9.mem = s.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨(((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8 (by decide)
      (by decide)).upd u9 (by decide) (by decide), by rw [m9]; exact hx⟩, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.gpr,
        u1.gpr, hc.ebp]
    · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.gpr, u3.gpr, hc.ebp,
        u2.other, u1.other]
    · rw [u9.gpr]
    · have hb32 : b < 2 ^ 32 := by omega_arith
      have hl32 : lb σ < 2 ^ 32 := by have := hlb σ; omega_arith
      rw [u9.other _ (by decide), u8.gpr, ifz, u6.gpr, u5.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hx.2.2.1, hg.aFr ok sLb (by decide), hslb σ _ hx.1, zmask_xor hb32 hl32]
      rfl
  · -- The selection.
    refine (sel_vp h hg (c := fun σ => b = lb σ) (X := X3)).mono
      (fun σ s ⟨⟨hc, hx⟩, si, di, cx, dx⟩ => ⟨hc, hx, si, di, cx, dx⟩)
      fun σ s ⟨hc, m₀, ⟨hi, hy, hbi, hst, hsel⟩, fr, hb'⟩ => ⟨hc, hI σ _ _ hi (fr.sub inL), ?_, ?_, ?_, ?_⟩
    · exact sbytes_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith))
        (by omega_arith) hy
    · exact slot_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sl sBi (by decide) (by omega_arith)) hbi
    · rw [stateAt_keep h fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)), hst]
    · intro hl
      by_cases e : b = lb σ
      · rw [← e, ← hst]
        refine h.ok.reloc _ _ _ _ fun i hi' => ?_
        rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa, hb' i hi', ite_eq_left e]
        simp only [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      · have hl' : lb σ < b := by omega_arith
        rw [← hsel hl']
        refine h.md.stateAt_congr fun i hi' => ?_
        rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa, hb' i hi', ite_eq_right e]
  · -- The next block.
    refine ((VP.syms (VP.taint (G := fun σ s => isa.eval .ne s = some (decide (0 < n)) ∧
        (n = 0 → Ctx L scr σ s ∧ Inv σ s.mem ∧ h.md.stateAt s.mem (sa scr oSel) =
          h.md.compressList h.ok.iv (ylist (yv σ) T) (lb σ + 1)) ∧ (0 < n → n ≤ nbm ∧ CS (nbm - n) σ s))
      [.esp, .ebp] compNext_taint (sp_bp fun _ _ h => h.1)
      fun σ s ⟨hc, hi, hy, hbi, hst, hsel⟩ => ?_)).mono (fun _ _ h => h)
      fun σ s ⟨⟨e, h0, hp⟩, sy⟩ => ⟨e, fun x => ⟨h0 x, sy⟩, fun x => ⟨hp x, sy⟩⟩)
    simp only [compNext, ld, st, addi, Impl.RsaPkcs1Sig.X86.stk]
    refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => wp_addi fun t2 u2 => ?_
    refine (c1.upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 u3 => ?_
    refine wp_cmpm (B := L.B) (by rw [c3.st.sp]) (by rw [hg.aFr ok sNb (by decide)]; exact c3.rFr hg sNb (by decide))
      fun t4 u4 _ z => WP.block_nil ?_
    have e2 : t2.gpr .eax = BitVec.ofNat 32 (b + 1) := by
      rw [u2.gpr, u1.gpr, hbi, BitVec.ofNat_add_ofNat]
    have m4 : t4.mem = s.mem.writeW (L.fr sBi) (BitVec.ofNat 32 (b + 1)) := by
      rw [u4.mem, u3.mem, e2, u2.mem, u1.mem]
    have fr : Frame [slotR L sBi] s.mem t4.mem := by rw [m4]; exact slot_frame L _ _ _
    have hc' : Ctx L scr σ t4 := c3.fupd u4
    have hi' : Inv σ t4.mem := hI σ _ _ hi (fr.sub inB)
    have hsel' : lb σ < b + 1 → h.md.stateAt t4.mem (sa scr oSel) =
        h.md.compressList h.ok.iv (ylist (yv σ) T) (lb σ + 1) := fun hl => by
      rw [stateAt_keep h fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (sl sBi (by decide) (by omega_arith)).symm), hsel hl]
    rw [u3.gpr, u3.mem, e2, u2.mem, u1.mem, hg.aFr ok sNb (by decide),
      Lay.readW_fr_other (d := sNb) (e := sBi) L _ _ (by decide) (by decide) (by decide), hsn σ _ hi,
      sub_beq (a := b + 1) (b := nbm) (by omega_arith) (by omega_arith)] at z
    refine ⟨?_, fun h0 => ⟨hc', hi', hsel' (by have := hlb σ; omega_arith)⟩, fun hp => ⟨by omega_arith, ?_⟩⟩
    · show eval .ne t4 = _
      simp only [eval, z]
      by_cases h0 : n = 0
      · simp [h0]; omega_arith
      · have h1 : 0 < n := Nat.pos_of_ne_zero h0
        simp [h1]; omega_arith
    rw [show nbm - n = b + 1 by omega_arith]
    refine ⟨hc', hi', ⟨sbytes_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (sl sBi (by decide) (by omega_arith)).symm) (by omega_arith) hy,
      by rw [m4, Mem.readW_writeW_self32], ?_, hsel'⟩⟩
    rw [stateAt_keep h fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (sl sBi (by decide) (by omega_arith)).symm), hst]

end VG.Proof.RsaPss.X86

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)
open VG.Impl.RsaOaep.X86 (sTab)
open VG.Proof.RsaOaep.X86 (VP.syms)

variable {L : Lay} {scr : BitVec 32} (h : PssHash) {dn : String} {f : MdFns} {p ai ac ad : BitVec 32}

/-- `ctHash`: the digest of the message in `Y`, of a length in its slot,
padded in `nbm` blocks. -/
theorem ctHashR_vp (hg : Geo L scr) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {msg : State → List Byte} (hfit : ∀ σ, (msg σ).length + 1 + h.L ≤ nbm * h.B) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame (ctW h L scr (nbm * h.B)) m m' → Inv σ m')
    (hsl : ∀ σ m, Inv σ m → m.readW (L.fr sL) 32 = BitVec.ofNat 32 (msg σ).length)
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm) (hd : DigCerts h)
    (hTab : TabAt L h dn f p ai ac ad Inv) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = (msg σ).getD i 0) ∧
        s.syms = σ.syms)
      (seqs [initPartT f, lenPart h.H, padPart h.H, compLoopT f h.H, outPartT f])
      (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧
        ∀ i < h.D, s.mem (sa scr (oDig + i)) = (h.ok.hH.SH.H.hash (msg σ)).getD i 0) ∧ s.syms = σ.syms) := by
  have hN := h.N_le
  have hB := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have hNL := h.NL
  have hDN := h.D_le
  have hso := h.so_le
  have fit := hg.fit
  unfold oRsa at fit
  have hB0 : 0 < h.B := by omega_arith
  have hLB : h.L < h.B := by have := h.D_pos; omega_arith
  obtain ⟨σ', ok⟩ := hg.ok
  have hC : L.C ≤ 2 ^ 32 := by have := ok.BC; have := L.B.isLt; omega_arith
  have hIs : ∀ rs : List Region, (∀ r ∈ rs, r ∈ ctW h L scr (nbm * h.B)) →
      ∀ σ m m', Inv σ m → Frame rs m m' → Inv σ m' :=
    fun rs hs σ m m' hi hf => hI σ m m' hi (hf.mono hs)
  have hq : ∀ σ, ((msg σ).length + h.L) / h.B < nbm := fun σ =>
    (Nat.div_lt_iff_lt_mul hB0).2 (by have := hfit σ; omega_arith)
  have hℓ : ∀ σ, (msg σ).length < 2048 := fun σ => by have := hfit σ; omega_arith
  have sl : ∀ d, d + 4 ≤ frameBytes → ∀ {o n : Nat}, o + n ≤ oRsa → (slotR L d).Disjoint (sR scr o n) :=
    fun d hd o n h => hg.slot ok h (by rw [hg.F]; omega_arith)
  show VP _ (.seq (initPartT f) (.seq (lenPart h.H) (.seq (padPart h.H) (.seq (compLoopT f h.H) (outPartT f))))) _
  -- The hash value initialized.
  refine VP.seq (initT_vp h hg (Inv := fun σ m => Inv σ m ∧ ∀ i < nbm * h.B, m (sa scr (oY + i)) = (msg σ).getD i 0)
    (fun σ m m' ⟨hi, hy⟩ hf => ⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp) σ m m' hi hf,
      sbytes_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Geo.sep (by pomega) (by pomega) (by pomega)
        · exact hg.low ok (by pomega)) (by pomega) hy⟩) (TabAt.mono h hTab fun _ _ x => x.1)) ?_
  -- The length field.
  refine VP.seq (VP.syms (((lenBlk_vp h hg (ℓ := fun σ => (msg σ).length) (Inv := fun σ m =>
      (Inv σ m ∧ ∀ i < nbm * h.B, m (sa scr (oY + i)) = (msg σ).getD i 0) ∧
        h.md.stateAt m (sa scr oSt) = h.ok.iv)
    (fun σ m m' ⟨⟨hi, hy⟩, he⟩ hf => ⟨⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp) σ m m' hi hf,
      sbytes_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Geo.sep (by pomega) (by pomega) (by pomega)
        · exact (sl sLb (by decide) (by pomega)).symm) (by pomega) hy⟩,
      (stateAt_keep h hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Geo.sep (by pomega) (by pomega) (by pomega)
        · exact (sl sLb (by decide) (by pomega)).symm).trans he⟩)
    fun σ => by have := hℓ σ; omega_arith)).mono
      (fun σ s ⟨hc, hi, he⟩ => ⟨hc, ⟨hi, he⟩, hsl σ _ hi.1⟩) fun _ _ h => h)) ?_
  -- The padding.
  refine VP.seq (VP.syms ((pad_vp h hg hnb hnb0 hfit (Inv := fun σ m => Inv σ m ∧ h.md.stateAt m (sa scr oSt) = h.ok.iv)
    (fun σ m m' ⟨hi, he⟩ hf => ⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp) σ m m' hi hf,
      (stateAt_keep h hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)).trans he⟩)
    (fun σ m hi => hsn σ m hi.1)).mono
      (fun σ s ⟨hc, ⟨⟨hi, hy⟩, he⟩, lb, sl', slb⟩ => ⟨hc, ⟨hi, he⟩, lb, sl', slb, hy⟩) fun _ _ h => h)) ?_
  -- Every block compressed.
  refine VP.seq ((compLoopT_vp h hg hnb hnb0 (lb := fun σ => ((msg σ).length + h.L) / h.B)
    (yv := fun σ i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) hq
    (Inv := fun σ m => Inv σ m ∧ m.readW (L.fr sLb) 32 = BitVec.ofNat 32 (((msg σ).length + h.L) / h.B))
    (fun σ m m' ⟨hi, hb⟩ hf => ⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) σ m m' hi hf,
      slot_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact sl sLb (by decide) (by pomega)
        · exact sl sLb (by decide) (by pomega)
        · exact sl sLb (by decide) (by pomega)
        · exact Lay.fr_sep (by decide) (by decide) (by decide)
        · exact Lay.fr_low (by decide) hC) hb⟩)
    (fun σ m hi => hi.2) (fun σ m hi => hsn σ m hi.1) (TabAt.mono h hTab fun _ _ x => x.1)).mono
      (fun σ s ⟨⟨hc, ⟨hi, he⟩, _, _, slb, hy⟩, sy⟩ => ⟨⟨hc, ⟨hi, slb⟩, hy, he⟩, sy⟩) fun _ _ h => h) ?_
  -- The digest.
  refine (outT_vp h hg hd (X := fun σ m => (Inv σ m ∧ m.readW (L.fr sLb) 32 =
      BitVec.ofNat 32 (((msg σ).length + h.L) / h.B)) ∧ h.md.stateAt m (sa scr oSel) =
      h.md.compressList h.ok.iv (ylist (fun i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) (nbm * h.B))
        (((msg σ).length + h.L) / h.B + 1)) (TabAt.mono h hTab fun _ _ x => x.1.1)).mono (fun _ _ h => h)
      fun σ s ⟨⟨hc, m₀, ⟨⟨hi, _⟩, he⟩, hf, hm⟩, sy⟩ => ?_
  refine ⟨⟨hc, hIs _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp) σ _ _ hi hf, fun i hi => ?_⟩, sy⟩
  rw [hm i (by omega_arith), he, h.ok.link.hash]
  have hq1 : ((msg σ).length + h.L) / h.B + 1 ≤ nbm := hq σ
  have key : h.md.compressList h.ok.iv
      (ylist (fun i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) (nbm * h.B))
        (((msg σ).length + h.L) / h.B + 1) =
      h.md.compressList h.ok.iv (h.md.pad (msg σ)) ((h.md.pad (msg σ)).length / h.B) := by
    rw [RsaPss.pad_length h.md _ hB0 hLB, Nat.mul_div_cancel_left _ hB0]
    refine h.md.compressList_congr fun j hj => ?_
    have hT : j < nbm * h.B := by
      have := Nat.mul_le_mul_left h.B hq1
      rw [Nat.mul_comm h.B nbm] at this
      omega_arith
    rw [ylist_getD hT, padY_eq hB0 hLB _ _ hj, RsaPss.pad_getD h.md _ hB0 hLB hj]
  rw [key, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  rfl

/-- What `ctHashT` writes: `ctHash`'s and the slot of the table. -/
abbrev ctWT (L : Lay) (scr : BitVec 32) (T : Nat) : List Region := slotR L sTab :: ctW h L scr T

/-- `ctHashT f h.H j`: the digest of the message in `Y`, of a length in its
slot, padded in `nbm` blocks, with the hash function of the table that is
our argument `j`, at `L.argv`'s word `j`. -/
theorem ctHashT_vp (hg : Geo L scr) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {msg : State → List Byte} (hfit : ∀ σ, (msg σ).length + 1 + h.L ≤ nbm * h.B) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame (ctWT h L scr (nbm * h.B)) m m' → Inv σ m')
    (hsl : ∀ σ m, Inv σ m → m.readW (L.fr sL) 32 = BitVec.ofNat 32 (msg σ).length)
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm) (hd : DigCerts h)
    {j : Nat} (hj : j < L.argv.length) (hcj : TaintOk [.esp, .ebp] (.block (hTab j)))
    (hH : ∀ σ m, Inv σ m → HFacts h dn f (L.argv.getD j 0) ai ac ad σ)
    (tbl : ∀ k, k < 5 → ∃ R ∈ L.ro, R.Contains (VG.X86.addr (L.argv.getD j 0) (4 * k)) 4)
    (fne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = (msg σ).getD i 0) ∧
        s.syms = σ.syms)
      (ctHashT f h.H j)
      (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧
        ∀ i < h.D, s.mem (sa scr (oDig + i)) = (h.ok.hH.SH.H.hash (msg σ)).getD i 0) ∧ s.syms = σ.syms) := by
  obtain ⟨σ', ok⟩ := hg.ok
  have fit := hg.fit
  unfold oRsa at fit
  have hN := h.N_le
  have hB := h.B_le
  have hso := h.so_le
  have hC : L.C ≤ 2 ^ 32 := by have := ok.BC; have := L.B.isLt; omega_arith
  have sl : ∀ d, d + 4 ≤ frameBytes → ∀ {o n : Nat}, o + n ≤ oRsa → (slotR L d).Disjoint (sR scr o n) :=
    fun d hd o n h => hg.slot ok h (by rw [hg.F]; omega_arith)
  have dT : ∀ r ∈ ctW h L scr (nbm * h.B), (slotR L sTab).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl _ (by decide) (by pomega)
    · exact Lay.fr_low (by decide) hC
    · exact sl _ (by decide) (by pomega)
    · exact Lay.fr_sep (by decide) (by decide) (by decide)
    · exact sl _ (by decide) (by pomega)
    · exact sl _ (by decide) (by pomega)
    · exact sl _ (by decide) (by pomega)
    · exact Lay.fr_sep (by decide) (by decide) (by decide)
    · exact sl _ (by decide) (by pomega)
  show VP _ (.seq (.block (hTab j)) (seqs [initPartT f, lenPart h.H, padPart h.H, compLoopT f h.H, outPartT f])) _
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ (Inv σ s.mem ∧ s.mem.readW (L.fr sTab) 32 = L.argv.getD j 0) ∧
      ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = (msg σ).getD i 0) ∧ s.syms = σ.syms)
    (VP.syms (VP.taint [.esp, .ebp] hcj (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, hy⟩ => ?_)) ?_
  · simp only [hTab, ld, st, Impl.RsaPkcs1Sig.X86.stk]
    refine hc.wp_arg hg hj (by decide) (by decide) fun t1 c1 u1 => c1.wp_st hg (by decide) fun t2 c2 u2 =>
      WP.block_nil ?_
    have fr : Frame [slotR L sTab] s.mem t2.mem := by rw [u2.mem, u1.mem]; exact slot_frame L _ _ _
    refine ⟨c2, ⟨hI σ _ _ hi (fr.sub fun r hr => ⟨r, by simp at hr; subst hr; simp [ctWT], fun _ h => h⟩),
      by rw [u2.mem, Mem.readW_writeW_self32, u1.gpr]⟩, sbytes_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (sl sTab (by decide) (by pomega)).symm) (by pomega) hy⟩
  · refine (ctHashR_vp h hg hnb hnb0 hfit (Inv := fun σ m => Inv σ m ∧ m.readW (L.fr sTab) 32 = L.argv.getD j 0)
      (fun σ m m' ⟨hi, ht⟩ fr => ⟨hI σ m m' hi (fr.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩),
        slot_keep fr dT ht⟩)
      (fun σ m h => hsl σ m h.1) (fun σ m h => hsn σ m h.1) hd
      ⟨fun σ m h => hH σ m h.1, fun σ m h => h.2, tbl, fne⟩).mono (fun _ _ h => h)
      fun σ s ⟨⟨hc, ⟨hi, _⟩, hdg⟩, sy⟩ => ⟨⟨hc, hi, hdg⟩, sy⟩

end VG.Proof.RsaPss.X86
