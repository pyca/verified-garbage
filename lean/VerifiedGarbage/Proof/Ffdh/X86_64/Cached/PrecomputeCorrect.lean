module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeContract
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Main
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Table
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute

/-! # FFDH's context on x86-64: the arguments, the domain's recognition and the modulus check -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Ffdh.X86_64.Cached
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The precomputation's data, from the registers on entry. -/
def pcOf (s : State) : PcP :=
  ⟨s.gpr .r9, (stackArg s 0).toNat * 8, (s.gpr .r8).toNat, (s.gpr .rcx).toNat, s.gpr .rdx, pcDom s, s.gpr .rdi⟩

/-- What the precondition gives. -/
structure PcG (s : State) : Prop where
  k1 : 64 ≤ (pcOf s).k
  k2 : (pcOf s).k ≤ 1024
  dl : (pcOf s).dl = 2 * (pcOf s).k ∨ (pcOf s).dl = 3 * (pcOf s).k
  n : (s.gpr .rsi).toNat = (pcOf s).n
  hZ : 128 * (pcOf s).k + 256 ≤ (pcOf s).Z
  scr : Scr s (pcOf s).B (pcOf s).Z
  dom : Src s (pcOf s).B (pcOf s).Z (pcOf s).dp (pcOf s).dom
  domRd : InRegions (s.rd ++ s.wr) (pcOf s).dp (pcOf s).dl
  ctx : CtxRegion s (pcOf s).B (pcOf s).Z (pcOf s).cp (pcOf s).n
  dsep : ∀ i < (pcOf s).dl, 8 * (pcOf s).n ≤ ofs (pcOf s).cp ((pcOf s).dp + BitVec.ofNat 64 i)
  valid : Spec.Ffdh.domainValid (pcOf s).k (pcOf s).dom = true
  consts : ConstsOk tableConsts 0 s
  scrWr : (⟨(pcOf s).B, (pcOf s).Z⟩ : Region) ∈ s.wr
  retCtx : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨(pcOf s).cp, 8 * (pcOf s).n⟩
  retScr : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨(pcOf s).B, (pcOf s).Z⟩

theorem precomputedWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = 3 + 34 * ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth,
    Spec.Rsa.modulusWords]
  omega

theorem pcG_of {s : State} (h : pcContract.pre s) : PcG s := by
  obtain ⟨hp, hc⟩ := h
  obtain ⟨_, hrd, hwr, dcd, dcs, _, dds, _, nc, nd, ns, rc, _, rs, _, ⟨k1, k2⟩, hdl, hn, hsw, hv⟩ := hp
  have sa : stackArg (stripConsts tableConsts s) 0 = stackArg s 0 := rfl
  simp only [stripConsts_gpr, stripConsts_mem, stripConsts_wr, sa] at *
  have hn' : (s.gpr .rsi).toNat = 3 + 34 * (((s.gpr .r8).toNat + 7) / 8) := by
    rw [hn, precomputedWords_eq]
  have memRd : ∀ r ∈ (stripConsts tableConsts s).rd, r ∈ s.rd := fun r hr => List.mem_of_mem_take hr
  have hdom : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region) ∈ s.rd ++ s.wr :=
    List.mem_append_left _ (memRd _ (by rw [hrd]; simp))
  have hctx : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hscr : (⟨s.gpr .r9, (stackArg s 0).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  unfold Spec.Rsa.scratchWords at hsw
  have hrl : (s.gpr .rcx).toNat ≤ 2 ^ 64 := Nat.le_of_lt (s.gpr .rcx).isLt
  refine ⟨k1, k2, hdl, hn', by dsimp only [pcOf]; omega, Scr.of_mem hscr ns,
    src_of_region hdom hrl dds, ⟨_, hdom, Region.contains_self _ _⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, hv, hc, hscr,
    ?_, rs⟩
  · intro i hi
    exact ⟨_, hctx, by
      rw [show ((pcOf s).n) = (s.gpr .rsi).toNat from hn'.symm] at hi
      exact Offset.contains_base _ (by omega) (by omega)⟩
  · intro i hi
    exact ⟨_, List.mem_append_right _ hctx, by
      rw [show ((pcOf s).n) = (s.gpr .rsi).toNat from hn'.symm] at hi
      exact Offset.contains_base _ (by omega) (by omega)⟩
  · intro i hi
    rw [show ((pcOf s).n) = (s.gpr .rsi).toNat from hn'.symm] at hi
    exact out_scr dcs (contains_byte _ (by omega) (by omega))
  · dsimp only [pcOf, PcP.n, PcP.w]; omega
  · intro i hi
    have d : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rdi, 8 * (pcOf s).n⟩ := by
      rw [show 8 * (pcOf s).n = (s.gpr .rsi).toNat * 8 by dsimp only [pcOf, PcP.n, PcP.w]; omega]
      exact Region.Disjoint.symm dcd
    exact out_scr d (contains_byte _ hi hrl)
  · rw [show 8 * (pcOf s).n = (s.gpr .rsi).toNat * 8 by dsimp only [pcOf, PcP.n, PcP.w]; omega]
    exact rc

/-! ## The entry -/

/-- The header after the entry: the six saved registers, the context and
the scan's two arguments, in `sDom` and `sDomLen`. -/
def pcEntryMem (s : State) : Mem :=
  ((((((((s.mem.writeW (off (s.gpr .r9) (8 * 0)) (s.gpr .rbx)).writeW (off (s.gpr .r9) (8 * 1)) (s.gpr .rbp)).writeW
    (off (s.gpr .r9) (8 * 2)) (s.gpr .r12)).writeW (off (s.gpr .r9) (8 * 3)) (s.gpr .r13)).writeW
    (off (s.gpr .r9) (8 * 4)) (s.gpr .r14)).writeW (off (s.gpr .r9) (8 * 5)) (s.gpr .r15)).writeW
    (off (s.gpr .r9) (8 * sCtx)) (s.gpr .rdi)).writeW (off (s.gpr .r9) (8 * sDom)) (s.gpr .rcx)).writeW
    (off (s.gpr .r9) (8 * sDomLen)) (s.gpr .r8)

theorem pcEntryMem_facts (s : State) :
    let m := pcEntryMem s
    word m (s.gpr .r9) (8 * 0) = s.gpr .rbx ∧ word m (s.gpr .r9) (8 * 1) = s.gpr .rbp ∧
    word m (s.gpr .r9) (8 * 2) = s.gpr .r12 ∧ word m (s.gpr .r9) (8 * 3) = s.gpr .r13 ∧
    word m (s.gpr .r9) (8 * 4) = s.gpr .r14 ∧ word m (s.gpr .r9) (8 * 5) = s.gpr .r15 ∧
    word m (s.gpr .r9) (8 * sCtx) = s.gpr .rdi ∧ word m (s.gpr .r9) (8 * sDom) = s.gpr .rcx ∧
    word m (s.gpr .r9) (8 * sDomLen) = s.gpr .r8 ∧ Outside (s.gpr .r9) 0 (8 * 32) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m pcEntryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

theorem pcEntry_ok {s : State} (g : PcG s) :
    WP isa (.block Precompute.entry) s fun t =>
      t.gpr .rdi = s.gpr .rdx ∧ t.mem = pcEntryMem s ∧ Keep [.rdi] s t := by
  have hZ := g.hZ
  have hk := g.k1
  have hw : ∀ i < 32, InRegions s.wr (off (s.gpr .r9) (8 * i)) 8 := fun i hi =>
    g.scr.st (by dsimp only [pcOf] at hZ ⊢; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = s.gpr .rdx ∧ t.mem = pcEntryMem s) ?_ rfl)
    fun t ⟨⟨hd, hm⟩, k⟩ => ⟨hd, hm, k⟩
  have e128 : BitVec.ofInt 64 ((128 : Nat) : Int) = BitVec.ofNat 64 (8 * sDom) := rfl
  have e136 : BitVec.ofInt 64 ((136 : Nat) : Int) = BitVec.ofNat 64 (8 * sDomLen) := rfl
  have w128 : InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 (8 * sDom)) 8 := hw sDom (by decide)
  have w136 : InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 (8 * sDomLen)) 8 := hw sDomLen (by decide)
  unfold Precompute.entry save
  simp only [saved, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.ws, at_, hdrOff, hw 0 (by decide), hw 1 (by decide),
    hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sCtx (by decide),
    e128, e136, w128, w136]
  rfl

theorem frame_of_inScr {B : Addr} {Z : Nat} {m m' : Mem} (h : InScr B Z m m') : Frame [⟨B, Z⟩] m m' :=
  fun x hx => h x (by
    rcases Nat.lt_or_ge (ofs B x) Z with hl | hl
    · exact absurd (contains_scr hl) (hx _ List.mem_cons_self)
    · exact hl)

theorem Src.bytes {s : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs) :
    Spec.Rsa.bytesAt s.mem p bs.length = bs := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · intro i h₁ h₂
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.val i h₂

theorem pcDom_length (s : State) : (pcOf s).dom.length = (pcOf s).dl := by
  simp only [pcOf, pcDom, Spec.Rsa.bytesAt, List.length_map, List.length_range]

/-! ## The recognition and the modulus check -/

/-- The header once the scan's result and `Domain`'s arguments are stored. -/
def afterMem (m : Mem) (B : Addr) (r d L k : BitVec 64) : Mem :=
  (((m.writeW (off B (8 * sRec)) r).writeW (off B (8 * sDom)) d).writeW (off B (8 * sDomLen)) L).writeW
    (off B (8 * sK)) k

theorem afterMem_facts (m : Mem) (B : Addr) (r d L k : BitVec 64) :
    let m' := afterMem m B r d L k
    word m' B (8 * sRec) = r ∧ word m' B (8 * sDom) = d ∧ word m' B (8 * sDomLen) = L ∧
      word m' B (8 * sK) = k ∧ Outside B 0 (8 * 32) m m' ∧
      ∀ i < 32, i ≠ sRec → i ≠ sDom → i ≠ sDomLen → i ≠ sK → word m' B (8 * i) = word m B (8 * i) := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i hi h₁ h₂ h₃ h₄ => ?_⟩ <;> unfold m' afterMem
  · repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) | exact word_writeW_self _ _ _ _)
  · repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) | exact word_writeW_self _ _ _ _)
  · repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) | exact word_writeW_self _ _ _ _)
  · exact word_writeW_self _ _ _ _
  · repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)
  · refine word_skip (word_skip (word_skip (word_skip rfl ?_ (by decide) hi) ?_ (by decide) hi) ?_ (by decide) hi)
      ?_ (by decide) hi <;> intro e <;> subst e <;> contradiction

theorem afterScan_ok {t : State} {B : Addr} {Z : Nat} (hs : Scr t B Z) (hZ : 256 ≤ Z)
    (hb : t.gpr .r9 = B) {L : BitVec 64} (hl : word t.mem B (8 * sDom) = L) :
    WP isa (.block Precompute.afterScan) t fun u => u.gpr .rdi = B ∧
      u.mem = afterMem t.mem B (t.gpr .rax) (t.gpr .rdi) L (t.gpr .r8) ∧ Keep [.rcx, .rdi] t u := by
  have hw : ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun i hi => hs.st (by omega)
  have e128 : BitVec.ofInt 64 ((128 : Nat) : Int) = BitVec.ofNat 64 (8 * sDom) := rfl
  have hr : ∀ v : BitVec 64, (t.mem.writeW (off B (8 * sRec)) v).readW (B + BitVec.ofNat 64 (8 * sDom)) 64 = L :=
    fun v => word_skip hl (by decide) (by decide) (by decide)
  have r128 : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 (8 * sDom)) 8 := hs.ld (by unfold sDom sFn; omega)
  refine WP.mono (WP.keep [.rcx, .rdi] (Q := fun u => u.gpr .rdi = B ∧
    u.mem = afterMem t.mem B (t.gpr .rax) (t.gpr .rdi) L (t.gpr .r8)) ?_ rfl)
    fun u ⟨⟨hd, hm⟩, k⟩ => ⟨hd, hm, k⟩
  unfold Precompute.afterScan
  xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.ws, at_, hdrOff, hb, e128, hr, r128, hw sRec (by decide),
    hw sDom (by decide), hw sDomLen (by decide), hw sK (by decide)]
  rfl

theorem ofNat_toNat' (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- What the modulus check leaves for `main`. -/
structure StartPost (s v : State) : Prop where
  zf : v.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip ((pcOf s).dom.take (pcOf s).k)) (pcOf s).k)
  main : MainPre (pcOf s) v
  saved : ∀ i < 6, word v.mem (pcOf s).B (8 * i) = s.gpr (saved.getD i .rax)
  scr : InScr (pcOf s).B (pcOf s).Z s.mem v.mem
  keep : Keep (.rdi :: mmRegs) s v

theorem start_then {s : State} (g : PcG s) {c : Prog isa} {Q : State → Prop}
    (h : ∀ v, StartPost s v → WP isa c v Q) :
    WP isa (.seq (.block Precompute.entry) (.seq (VG.Impl.Ffdh.X86_64.VettedValidation.scan
      VG.Impl.Ffdh.VettedGroups.groups 0) (.seq (.block (Precompute.afterScan ++ domHead)) c))) s Q := by
  have hZ := g.hZ
  have hk := g.k1
  have hk2 := g.k2
  have hdl := g.dl
  refine WP.seq (WP.mono_syms (pcEntry_ok g) fun u ⟨hdU, hmU, kU⟩ symU => ?_)
  obtain ⟨e0, e1, e2, e3, e4, e5, eC, eD, eL, eO⟩ := pcEntryMem_facts s
  rw [← hmU] at e0 e1 e2 e3 e4 e5 eC eD eL eO
  have iU : InScr (pcOf s).B (pcOf s).Z s.mem u.mem := InScr.of_outside eO (by dsimp only [pcOf] at hZ ⊢; omega)
  have bU : u.gpr .r9 = (pcOf s).B := kU.gpr (by decide)
  have scrU : Scr u (pcOf s).B (pcOf s).Z := g.scr.congr kU.2.2
  have domU : Src u (pcOf s).B (pcOf s).Z (pcOf s).dp (pcOf s).dom := g.dom.congrK iU kU
  have ctxU : VG.Proof.Ffdh.X86_64.VettedValidation.Context (pcOf s).B (pcOf s).dp (pcOf s).k (pcOf s).dom u :=
    ⟨bU, hdU, by rw [pcDom_length]; exact eD.trans (ofNat_toNat' _).symm,
      eL.trans (ofNat_toNat' _).symm, scrU.ld (d := 8 * sDom) (by unfold sDom sFn; dsimp only [pcOf] at hZ ⊢; omega),
      scrU.ld (d := 8 * sDomLen) (by unfold sDomLen sFn; dsimp only [pcOf] at hZ ⊢; omega),
      by rw [kU.2.1, kU.2.2, pcDom_length]; exact g.domRd, Src.bytes domU,
      by rw [pcDom_length]; exact hdl, hk, hk2⟩
  have tableU := VG.Proof.Ffdh.X86_64.VettedValidation.consts_table_after g.consts (frame_of_inScr iU) kU g.scrWr
  rw [← symU, ← BitVec.add_zero (u.syms _)] at tableU
  refine WP.seq (WP.mono (VG.Proof.Ffdh.X86_64.VettedValidation.scan_ok _ 0 u ctxU rfl tableU
    (by simpa only [Nat.zero_add, VG.Impl.Ffdh.VettedGroups.tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length))) fun t ⟨vT, mT, kT⟩ => ?_)
  have bT : t.gpr .r9 = (pcOf s).B := (kT.gpr (by decide)).trans bU
  have dT : t.gpr .rdi = s.gpr .rdx := (kT.gpr (by decide)).trans hdU
  have r8T : t.gpr .r8 = s.gpr .r8 := (kT.gpr (by decide)).trans (kU.gpr (by decide))
  have scrT : Scr t (pcOf s).B (pcOf s).Z := scrU.congr kT.2.2
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (afterScan_ok scrT (by dsimp only [pcOf] at hZ ⊢; omega) bT (L := s.gpr .rcx)
    (by rw [mT]; exact eD)) fun w ⟨dW, mW, kW⟩ => ?_
  obtain ⟨aR, aD, aL, aK, aO, aE⟩ := afterMem_facts t.mem (pcOf s).B (t.gpr .rax) (t.gpr .rdi) (s.gpr .rcx) (t.gpr .r8)
  rw [← mW] at aR aD aL aK aO aE
  have iW : InScr (pcOf s).B (pcOf s).Z t.mem w.mem := InScr.of_outside aO (by dsimp only [pcOf] at hZ ⊢; omega)
  have domW : Src w (pcOf s).B (pcOf s).Z (pcOf s).dp (pcOf s).dom :=
    (domU.congrK (by rw [mT]; exact InScr.refl _ _ _) kT).congrK iW kW
  have plen : ((pcOf s).dom.take (pcOf s).k).length = (pcOf s).k := by
    rw [List.length_take, pcDom_length]; omega
  refine WP.mono (domHead_ok (scrT.congr kW.2.2) dW (by dsimp only [pcOf] at hZ ⊢; omega) hk hk2
    (aD.trans dT) (aK.trans (r8T.trans (ofNat_toNat' _).symm)) (domW.take _) plen)
    fun v ⟨zV, gV, qV, fV, dV, kV⟩ => h v ?_
  have other : ∀ i < 32, i ≠ sG → i ≠ sQ → word v.mem (pcOf s).B (8 * i) = word w.mem (pcOf s).B (8 * i) :=
    fun i hi hg hq => fV.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega) (by omega)
  have iV : InScr (pcOf s).B (pcOf s).Z w.mem v.mem := InScr.of_frm fV (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> dsimp only [sG, sQ, sFn, pcOf] at hZ ⊢ <;> omega)
  have keep : Keep (.rdi :: mmRegs) s v := (((kU.trans kT).trans kW).trans kV).mono (by decide)
  refine ⟨zV, ⟨hk, hk2, hdl, pcDom_length s, hZ, g.scr.congr keep.2.2, dV, domW.congrK iV kV,
    g.ctx.congr keep.2.1 keep.2.2, g.dsep, ?_, g.valid⟩, ?_, ?_, keep⟩
  · intro e he
    simp only [PcP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [other _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)]; exact aD.trans dT
    · rw [other _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)]; exact aL.trans (ofNat_toNat' _).symm
    · rw [other _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)]; exact aK.trans (r8T.trans (ofNat_toNat' _).symm)
    · exact gV
    · exact qV
    · rw [other _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide), aE _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
        (by dsimp only; decide), mT]
      exact eC
    · rw [other _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)]; exact aR.trans vT
  · intro i hi
    rw [other i (by omega) (by unfold sG sFn; omega) (by unfold sQ sFn; omega),
      aE i (by omega) (by unfold sRec sY sFn; omega) (by unfold sDom sFn; omega)
        (by unfold sDomLen sFn; omega) (by unfold sK sFn; omega), mT]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [e0, e1, e2, e3, e4, e5]
  · exact (iU.trans (by rw [mT]; exact InScr.refl _ _ _)).trans (iW.trans iV)

/-! ## The computation, the branch and the exit -/

theorem main_ok (Mo : Mont) (R : R2Impl Mo) {p : PcP} {s : State} (h : MainPre p s) :
    WP isa (Precompute.main Mo.mm (.seq (.block r2Head) R.code)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 1 ∧ t.gpr .rdi = p.B ∧
        Spec.Rsa.wordsAt t.mem p.cp p.n = VG.Proof.Ffdh.generationValues p.k p.dom ∧
        (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ p.Only s.mem t.mem ∧
        Keep (.rdi :: mmRegs) s t := by
  unfold Precompute.main
  rw [show GenerateKey.bound ++ [Precompute.byteBits, .block (Precompute.width ++ Precompute.metadata),
      .block VG.Impl.Rsa.X86_64.head] ++ pSetup ++
      [.seq (.block r2Head) R.code, .block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)] ++
      Precompute.storePrefix ++ Precompute.table Mo.mm ++ [.block [VG.Impl.Rsa.X86_64.Crt.leave, .mov32 .rax (.imm 1)]] =
    (GenerateKey.bound ++ [Precompute.byteBits, .block (Precompute.width ++ Precompute.metadata)]) ++
      (([.block VG.Impl.Rsa.X86_64.head] ++ pSetup) ++
        ([.seq (.block r2Head) R.code, .block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)] ++
          (Precompute.storePrefix ++ (Precompute.table Mo.mm ++ [.block [VG.Impl.Rsa.X86_64.Crt.leave, .mov32 .rax (.imm 1)]]))))
    by simp only [List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_seqs_append (by simp [GenerateKey.bound]) (by simp) (WP.mono (front_ok h) fun u hf => ?_)
  refine WP.mono (inner_ok Mo R h hf) fun t ⟨hr, hd, hw, hs, ho, k⟩ =>
    ⟨hr, hd, hw, hs, ho, (hf.keep.trans k).mono (by decide)⟩

theorem _root_.VG.Proof.Ffdh.X86_64.Cached.PcP.Only.of_inScr {p : PcP} {m m' : Mem} (h : InScr p.B p.Z m m') :
    p.Only m m' := fun x hx _ => h x hx

theorem body_ok (Mo : Mont) (R : R2Impl Mo) {s : State} (g : PcG s) :
    WP isa (Precompute.body Mo.mm (.seq (.block r2Head) R.code)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 1 ∧ t.gpr .rdi = (pcOf s).B ∧
        Spec.Rsa.wordsAt t.mem (pcOf s).cp (pcOf s).n = VG.Proof.Ffdh.generationValues (pcOf s).k (pcOf s).dom ∧
        (∀ i < 6, word t.mem (pcOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ (pcOf s).Only s.mem t.mem ∧
        Keep (.rdi :: mmRegs) s t := by
  unfold Precompute.body
  refine start_then g fun v hv => ?_
  have mv := hv.main.modValid
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip ((pcOf s).dom.take (pcOf s).k)) (pcOf s).k)
    (by simp [eval, hv.zf]) (fun hf => ?_) (fun _ => ?_)
  · rw [mv] at hf
    contradiction
  · refine WP.mono (main_ok Mo R hv.main) fun t ⟨hr, hd, hw, hs, ho, k⟩ =>
      ⟨hr, hd, hw, fun i hi => (hs i hi).trans (hv.saved i hi), (PcP.Only.of_inScr hv.scr).trans ho,
        (hv.keep.trans k).mono (by decide)⟩

theorem pc_correct (Mo : Mont) (R : R2Impl Mo)
    (hmx : (Precompute.code Mo.mm (.seq (.block r2Head) R.code)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa (Precompute.code Mo.mm (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ pcContract.post s t := by
  have g := pcG_of h
  have hZ := g.hZ
  have hk := g.k1
  suffices hw : WP isa (Precompute.code Mo.mm (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ pcContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold Precompute.code
  refine WP.seq (WP.mono (body_ok Mo R g) fun u ⟨hr, hd, hw, hs, ho, k⟩ => ?_)
  refine WP.mono (exit_ok (g.scr.congr k.2.2) hd (by dsimp only [pcOf] at hZ ⊢; omega) hs)
    fun t ⟨hRestore, hm, kk⟩ => ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (kk.gpr (by decide)).trans (k.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    have hbyte := contains_byte (s.gpr .rsp) hi (by decide)
    exact ho _ (out_scr g.retScr hbyte) (out_scr g.retCtx hbyte)
  · change ((t.gpr .rax).setWidth 32) = 1
    rw [kk.gpr (show .rax ∉ saved by decide), hr]
    rfl
  · change Spec.Ffdh.generationPrecompute (s.gpr .r8).toNat (pcDom s) =
      some (Spec.Rsa.wordsAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    rw [hm, g.n]
    change _ = some (Spec.Rsa.wordsAt u.mem (pcOf s).cp (pcOf s).n)
    rw [hw]
    apply VG.Proof.Ffdh.generationPrecompute_eq
    · have := pcDom_length s
      have := g.dl
      change (pcOf s).k ≤ (pcOf s).dom.length
      omega
    · exact VG.Proof.Ffdh.domainValid_mod g.valid

end VG.Proof.Ffdh.X86_64.Cached
