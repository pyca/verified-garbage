module

public import VerifiedGarbage.Proof.RsaOaep.X86.Calls
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtMgfLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtXor
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3

/-!
# RSAES-OAEP on x86: `dst ⊕= MGF1(src, dstLen)`

`mgf_vp`: with `src` (`sl` bytes at `so`) and `dst` (`dl` bytes at `dOff`)
in `EM`'s place in our part of `scratch` (from `oEm` to `oBuf`), their
addresses and lengths in their slots, `mgfXor` XORs MGF1's mask of `src`
into `dst`, one digest of `src ‖ C` (by the streaming `init`, two `update`s
and `finalize`) at a time, as on ARMv7 (`Proof/RsaOaep/Arm/Mgf.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (oCW oSt oDig oEm oRsa frameBytes countLoop sCtr sDone xorBody mgfInit)
open VG.Proof.RsaPss.X86.Sg (vpAssoc)

variable {L : Lay} {scr : BitVec 32} (g : OHash)

/-- The bytes at `scr + o` as a list. -/
theorem bytesAt_scr (hg : Geo L scr) {m : Mem} {o n : Nat} (h : o + n ≤ oRsa) (hn : 0 < n) {xs : List Byte}
    (hl : xs.length = n) (hx : ∀ i < n, m (sa scr (o + i)) = xs.getD i 0) :
    Spec.Sha256.bytesAt m ((scr + BitVec.ofNat 32 o).setWidth 64) n = xs := by
  apply List.ext_getElem (by simp [Spec.Sha256.bytesAt, hl])
  intro i h1 h2
  simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Sha256.bytesAt, List.getElem_map, List.getElem_range]
  have e := hx i h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at e
  rw [← e, hg.scrA (by omega), sa, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-! ## The parameters -/

/-- What `mgfXor` writes. -/
abbrev mgfW (L : Lay) (scr : BitVec 32) (dOff dl : Nat) : List Region :=
  [sR scr oSt g.H.S, sR scr oCtr 4, sR scr oDig g.H.F, sR scr oCW g.ok.Wb, L.LOW, sR scr dOff dl, slotR L sCtr,
    slotR L sDone]

/-- The parameters of `mgfXor`: `src` (`sl` bytes at `so`) and `dst` (`dl`
bytes at `dOff`), apart, in `EM`'s place; their slots, and what the caller
keeps (`Inv`). -/
structure MP (L : Lay) (scr : BitVec 32) (so sl dOff dl : Nat) (seed : State → List Byte)
    (Inv : State → Mem → Prop) : Prop where
  hg : Geo L scr
  sl0 : 0 < sl
  dl0 : 0 < dl
  so0 : oEm ≤ so
  do0 : oEm ≤ dOff
  fs : so + sl ≤ oBuf
  fd : dOff + dl ≤ oBuf
  sep : so + sl ≤ dOff ∨ dOff + dl ≤ so
  sd : ∀ σ, (seed σ).length = sl
  I : ∀ σ m m', Inv σ m → Frame (mgfW g L scr dOff dl) m m' → Inv σ m'
  src : ∀ σ m, Inv σ m → m.readW (L.fr sSrc) 32 = scr + BitVec.ofNat 32 so
  srcL : ∀ σ m, Inv σ m → m.readW (L.fr sSrcLen) 32 = BitVec.ofNat 32 sl
  dst : ∀ σ m, Inv σ m → m.readW (L.fr sDst) 32 = scr + BitVec.ofNat 32 dOff
  dstL : ∀ σ m, Inv σ m → m.readW (L.fr sDstLen) 32 = BitVec.ofNat 32 dl

/-- The memory before iteration `c`: the counter, the bytes masked, `dst`
masked up to `c hLen` bytes, and `src`. -/
structure MB (L : Lay) (scr : BitVec 32) (so sl dOff dl c : Nat) (dstv : Nat → Byte) (seed : List Byte) (m : Mem) :
    Prop where
  ctr : m.readW (L.fr sCtr) 32 = BitVec.ofNat 32 c
  done : m.readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * g.H.D)
  dx : ∀ i < dl, m (sa scr (dOff + i)) =
    if i < c * g.H.D then dstv i ^^^ (Spec.Mgf1.mgf1 g.G seed dl).getD i 0 else dstv i
  sd : ∀ i < sl, m (sa scr (so + i)) = seed.getD i 0

variable {so sl dOff dl : Nat} {seed : State → List Byte} {Inv : State → Mem → Prop} {dstv : State → Nat → Byte}

/-- What the caller keeps, and the memory before iteration `c`. -/
abbrev MI (L : Lay) (scr : BitVec 32) (so sl dOff dl c : Nat) (dstv : State → Nat → Byte)
    (seed : State → List Byte) (Inv : State → Mem → Prop) (σ : State) (m : Mem) : Prop :=
  Inv σ m ∧ MB g L scr so sl dOff dl c (dstv σ) (seed σ) m

/-- What misses the slots of the counter and of the bytes masked, `dst` and `src`. -/
abbrev Away (L : Lay) (scr : BitVec 32) (so sl dOff dl : Nat) (r : Region) : Prop :=
  (slotR L sCtr).Disjoint r ∧ (slotR L sDone).Disjoint r ∧ (sR scr dOff dl).Disjoint r ∧ (sR scr so sl).Disjoint r

namespace MP

variable {g} (P : MP g L scr so sl dOff dl seed Inv)
include P

theorem keepB {c : Nat} {dv : Nat → Byte} {sd : List Byte} {m m' : Mem} {rs : List Region}
    (hm : MB g L scr so sl dOff dl c dv sd m) (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Away L scr so sl dOff dl r) : MB g L scr so sl dOff dl c dv sd m' := by
  have := P.fs; have := P.fd
  exact ⟨slot_keep hf (fun r hr => (hs r hr).1) hm.ctr, slot_keep hf (fun r hr => (hs r hr).2.1) hm.done,
    sbytes_keep hf (fun r hr => (hs r hr).2.2.1) (by oomega) hm.dx,
    sbytes_keep hf (fun r hr => (hs r hr).2.2.2) (by oomega) hm.sd⟩

theorem keep {c : Nat} {σ : State} {m m' : Mem} {rs : List Region}
    (hm : MI g L scr so sl dOff dl c dstv seed Inv σ m) (hf : Frame rs m m')
    (hsub : ∀ r ∈ rs, r ∈ mgfW g L scr dOff dl) (hs : ∀ r ∈ rs, Away L scr so sl dOff dl r) :
    MI g L scr so sl dOff dl c dstv seed Inv σ m' :=
  ⟨P.I σ m m' hm.1 (hf.mono hsub), P.keepB hm.2 hf hs⟩

/-- A range of our part of `scratch` before `EM` misses them. -/
theorem away_lo {o n : Nat} (hn : o + n ≤ oEm) : Away L scr so sl dOff dl (sR scr o n) := by
  have := P.fs; have := P.fd; have := P.so0; have := P.do0
  obtain ⟨σ', ok⟩ := P.hg.ok
  exact ⟨P.hg.slot ok (by oomega) (by rw [P.hg.F]; decide), P.hg.slot ok (by oomega) (by rw [P.hg.F]; decide),
    Geo.sep (by oomega) (by oomega) (by oomega), Geo.sep (by oomega) (by oomega) (by oomega)⟩

theorem away_low : Away L scr so sl dOff dl L.LOW := by
  have := P.fs; have := P.fd
  obtain ⟨σ', ok⟩ := P.hg.ok
  have hC : L.C ≤ 2 ^ 32 := by have := ok.BC; have := L.B.isLt; omega
  exact ⟨Lay.fr_low (by decide) hC, Lay.fr_low (by decide) hC, P.hg.low ok (by oomega), P.hg.low ok (by oomega)⟩

/-- So does a slot other than theirs. -/
theorem away_slot {d : Nat} (hd : d + 4 ≤ frameBytes) (h₁ : d + 4 ≤ sCtr ∨ sDone + 4 ≤ d) :
    Away L scr so sl dOff dl (slotR L d) := by
  have := P.fs; have := P.fd
  obtain ⟨σ', ok⟩ := P.hg.ok
  have hF : d + 4 ≤ L.F + 16 := by rw [P.hg.F]; omega
  refine ⟨slotSep (by decide) hd (by unfold sCtr sDone at *; omega),
    slotSep (by decide) hd (by unfold sCtr sDone at *; omega), (P.hg.slot ok (by oomega) hF).symm,
    (P.hg.slot ok (by oomega) hF).symm⟩

end MP

/-- The counter's bytes at `oCtr`. -/
abbrev Cb (scr : BitVec 32) (c : Nat) (m : Mem) : Prop := ∀ i < 4, m (sa scr (oCtr + i)) = (Spec.Rsa.i2osp c 4).getD i 0

/-- The digest of `src ‖ C` at `oDig`. -/
abbrev Dg (scr : BitVec 32) (x : List Byte) (m : Mem) : Prop :=
  ∀ i < g.H.D, m (sa scr (oDig + i)) = (g.ok.SH.H.hash x).getD i 0

/-- The memory after the XOR of iteration `c`. -/
structure DX (L : Lay) (scr : BitVec 32) (so sl dOff dl c : Nat) (dstv : Nat → Byte) (seed : List Byte) (m : Mem) :
    Prop where
  ctr : m.readW (L.fr sCtr) 32 = BitVec.ofNat 32 c
  done : m.readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * g.H.D)
  dx : ∀ i < dl, m (sa scr (dOff + i)) =
    if i < c * g.H.D + g.H.D then dstv i ^^^ (Spec.Mgf1.mgf1 g.G seed dl).getD i 0 else dstv i
  sd : ∀ i < sl, m (sa scr (so + i)) = seed.getD i 0

/-! ## The stages of an iteration -/

section Iter

variable {g} (P : MP g L scr so sl dOff dl seed Inv) (c : Nat)
include P

/-- The state set to the empty message. -/
theorem mgfA_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem)
      (.seq (.block initArgs) (callInit g.H))
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) []) := by
  have := g.S_le
  refine init_vp P.hg g.H g.ok (Inv := MI g L scr so sl dOff dl c dstv seed Inv) fun σ m m' hm hf =>
    P.keep hm hf (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact P.away_lo (by oomega)
    · exact P.away_low

/-- `update(state, 0, src, sl)`'s arguments. -/
theorem mgfB_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [])
      (.block updSrcArgs)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
        Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 so).setWidth 64) sl = seed σ ∧
        UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s) := by
  have hg := P.hg
  have := P.fs
  refine VP.taint [.esp, .ebp] updSrcArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, rp⟩ => ?_
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_movi fun t3 u3 => wp_movi fun t4 u4 => ?_
  have c4 : Ctx L scr σ t4 := (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3
    (by decide) (by decide)).upd u4 (by decide) (by decide)
  have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  refine c4.wp_slot hg (by decide) (by decide) (by decide) fun t5 c5 u5 =>
    c5.wp_slot hg (by decide) (by decide) (by decide) fun t6 c6 u6 => WP.block_nil ?_
  have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, m4]
  refine ⟨c6, m6 ▸ hm, m6 ▸ rp, rfl, by rw [m6]; exact bytesAt_scr hg (by oomega) P.sl0 (P.sd σ) hm.2.sd,
    ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.gpr]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
  · rw [u6.other _ (by decide), u5.gpr, m4, P.src σ _ hm.1]
  · rw [u6.gpr, u5.mem, m4, P.srcL σ _ hm.1]

/-- `update` absorbs `src`. -/
theorem mgfC_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
        Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 so).setWidth 64) sl = seed σ ∧
        UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s)
      (callUpd g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) := by
  have hg := P.hg
  have := P.fs; have := P.so0; have := g.S_le; have := g.Wb_le
  obtain ⟨σ', ok⟩ := hg.ok
  have aS : (scr + BitVec.ofNat 32 so).setWidth 64 = sa scr so := hg.scrA (by have := P.sl0; oomega)
  refine upd_vp hg g.H g.ok (msg := fun _ => []) (dat := seed) (c := 0) (Inv := MI g L scr so sl dOff dl c dstv seed Inv)
    (hg.rbuf (o := so) (n := sl) (by oomega) P.sl0)
    (by rw [aS]; exact Geo.sep (by oomega) (by oomega) (by oomega))
    (by rw [aS]; exact Geo.sep (by oomega) (by oomega) (by oomega)) (by rw [aS]; exact hg.low ok (by oomega))
    (by decide) fun σ m m' hm hf => P.keep hm hf (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact P.away_lo (by oomega)
    · exact P.away_lo (by oomega)
    · exact P.away_low

/-- The counter, big-endian, at `oCtr`. -/
theorem mgfD_vp (hc32 : c < 2 ^ 32) :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ))
      (.block ctrSet)
      (fun σ s => Ctx L scr σ s ∧ (MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧ Cb scr c s.mem) := by
  have hg := P.hg
  have := P.fs; have := g.S_le
  have fit := hg.fit
  unfold oRsa at fit
  refine VP.taint [.esp, .ebp] ctrSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, rp⟩ => ?_
  simp only [ctrSet, Impl.RsaPss.X86.ld, Impl.RsaPkcs1Sig.X86.at_]
  refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => wp_bswap fun t2 u2 => ?_
  have c2 : Ctx L scr σ t2 := c1.upd u2 (by decide) (by decide)
  have aW : VG.X86.addr scr oCtr = sa scr oCtr := hg.scrA (by oomega)
  refine wp_stm (B := scr) c2.ebp (by rw [aW]; exact hg.wr c2.st (by oomega)) fun t3 u3 => WP.block_nil ?_
  have e2 : t2.gpr .eax = bswap (BitVec.ofNat 32 c) := by rw [u2.gpr, u1.gpr, hm.2.ctr]
  have m3 : t3.mem = s.mem.writeW (sa scr oCtr) (bswap (BitVec.ofNat 32 c)) := by
    rw [u3.mem, aW, e2, u2.mem, u1.mem]
  have fr : Frame [sR scr oCtr 4] s.mem t3.mem := by
    rw [m3]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by oomega) (by oomega) (by oomega))
  refine ⟨ctxW hg hc fr (fun r hr => .inl ⟨oCtr, 4, by oomega, by simpa using hr⟩) (by rw [u3.rd, u2.rd, u1.rd])
      (by rw [u3.wr, u2.wr, u1.wr]) (by rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide)])
      (by rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide)]),
    ⟨P.keep hm fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact P.away_lo (by oomega),
      g.ok.repr _ _ _ _ _ (fun i hi => ?_) rp⟩, fun i hi => ?_⟩
  · exact fr.bytes (R := sR scr oSt g.H.S) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by oomega) (by oomega) (by oomega))
      (by show g.H.S ≤ 2 ^ 64; omega) hi
  rw [m3, sa_writeW32 scr _ _ (by oomega) (by oomega), ite_eq_left (by omega),
    show oCtr + i - oCtr = i by omega, ctrByte hc32 hi, i2osp4_getD c _ hi]

/-- `update(state, sl, scratch + oCtr, 4)`'s arguments. -/
theorem mgfE_vp :
    VP (fun σ s => Ctx L scr σ s ∧ (MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧ Cb scr c s.mem)
      (.block updCtrArgs)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
        Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 oCtr).setWidth 64) 4 = Spec.Rsa.i2osp c 4 ∧
        UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s) := by
  have hg := P.hg
  refine VP.taint [.esp, .ebp] updCtrArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hm, rp⟩, cb⟩ => ?_
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have c2 : Ctx L scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine c2.wp_slot hg (by decide) (by decide) (by decide) fun t3 c3 u3 => wp_movi fun t4 u4 => ?_
  refine wp_mov fun t5 u5 => wp_addi fun t6 u6 => wp_movi fun t7 u7 => WP.block_nil ?_
  have c7 : Ctx L scr σ t7 := (((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6
    (by decide) (by decide)).upd u7 (by decide) (by decide)
  have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨c7, m7 ▸ hm, m7 ▸ rp, by rw [List.nil_append, P.sd σ],
    by rw [m7]; exact bytesAt_scr hg (by oomega) (by decide) (i2osp4_length c) cb, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr,
      u2.mem, u1.mem, P.srcL σ _ hm.1]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
  · simp (disch := decide) only [u7.other, u6.gpr, u5.gpr, u4.other, u3.other, u2.other, u1.other, hc.ebp]
  · rw [u7.gpr]

/-- `update` absorbs the counter. -/
theorem mgfF_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
        Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 oCtr).setWidth 64) 4 = Spec.Rsa.i2osp c 4 ∧
        UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s)
      (callUpd g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4)) := by
  have hg := P.hg
  have := P.fs; have := g.S_le; have := g.Wb_le
  obtain ⟨σ', ok⟩ := hg.ok
  have aC : (scr + BitVec.ofNat 32 oCtr).setWidth 64 = sa scr oCtr := hg.scrA (by oomega)
  refine upd_vp hg g.H g.ok (msg := fun σ => [] ++ seed σ) (dat := fun _ => Spec.Rsa.i2osp c 4) (c := sl)
    (Inv := MI g L scr so sl dOff dl c dstv seed Inv) (hg.rbuf (o := oCtr) (n := 4) (by oomega) (by decide))
    (by rw [aC]; exact Geo.sep (by oomega) (by oomega) (by oomega))
    (by rw [aC]; exact Geo.sep (by oomega) (by oomega) (by oomega)) (by rw [aC]; exact hg.low ok (by oomega))
    (by oomega) fun σ m m' hm hf => P.keep hm hf (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact P.away_lo (by oomega)
    · exact P.away_lo (by oomega)
    · exact P.away_low

/-- `finalize(state, sl + 4, scratch + oDig)`'s arguments. -/
theorem mgfG_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4))
      (.block finArgs)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
        ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s) := by
  have hg := P.hg
  refine VP.taint [.esp, .ebp] finArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, rp⟩ => ?_
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have c2 : Ctx L scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine c2.wp_slot hg (by decide) (by decide) (by decide) fun t3 c3 u3 => wp_addi fun t4 u4 => wp_movi fun t5 u5 => ?_
  refine wp_mov fun t6 u6 => wp_addi fun t7 u7 => WP.block_nil ?_
  have c7 : Ctx L scr σ t7 := ((((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6
    (by decide) (by decide)).upd u7 (by decide) (by decide))
  have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨c7, m7 ▸ hm, m7 ▸ rp, by rw [List.length_append, List.nil_append, P.sd σ, i2osp4_length],
    ⟨?_, ?_, ?_, ?_⟩⟩
  · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.mem, u1.mem,
      P.srcL σ _ hm.1, BitVec.ofNat_add_ofNat]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr]; rfl
  · simp (disch := decide) only [u7.gpr, u6.gpr, u5.other, u4.other, u3.other, u2.other, u1.other, hc.ebp]

/-- `finalize` writes the digest. -/
theorem mgfH_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
        ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s)
      (callFin g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) := by
  have hg := P.hg
  have := P.fs; have := g.S_le; have := g.Wb_le; have := g.F_le; have := g.DF
  refine (fin_vp hg g.H g.ok (o := oDig) (c := sl + 4) (msg := fun σ => [] ++ seed σ ++ Spec.Rsa.i2osp c 4)
    (Inv := MI g L scr so sl dOff dl c dstv seed Inv)
    (.inr (by oomega)) (by oomega) (by oomega) (by oomega) fun σ m m' hm hf =>
      P.keep hm hf (fun r hr => ?_) fun r hr => ?_).mono
    (fun _ _ h => h) fun σ s ⟨hc, hm, hd⟩ => ⟨hc, hm, fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact P.away_lo (by oomega)
    · exact P.away_lo (by oomega)
    · exact P.away_lo (by oomega)
    · exact P.away_low
  · have e := congrArg (fun l => l.getD i 0) hd
    simp only [List.nil_append] at e
    rw [← e, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, Spec.Sha256.bytesAt,
      List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The XOR's registers. -/
theorem mgfI_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem)
      (.block (xorSet g.H))
      (fun σ s => Ctx L scr σ s ∧ (MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧
        s.gpr .edi = scr + BitVec.ofNat 32 (dOff + c * g.H.D) ∧ s.gpr .esi = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .ecx = BitVec.ofNat 32 (min g.H.D (dl - c * g.H.D))) := by
  have hD := g.D_le
  have hfd := P.fd
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] g.certs.xorSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, hd⟩ => ?_
  simp only [xorSet, Impl.RsaPss.X86.atS, Impl.RsaPss.X86.addSlot, Impl.RsaPss.X86.addi, Impl.RsaPss.X86.ld,
    Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
  have rS : ∀ {t : State} (d : Nat), Ctx L scr σ t → d + 4 ≤ frameBytes →
      InRegions (t.rd ++ t.wr) (VG.X86.addr L.B d) 4 := fun d ct hd => by
    rw [hg.aFr ok d hd]; exact ct.rFr hg d hd
  refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_addm (B := L.B) (by rw [c1.st.sp]) (rS sDone c1 (by decide)) fun t2 u2 => ?_
  have c2 : Ctx L scr σ t2 := c1.upd u2 (by decide) (by decide)
  refine wp_mov fun t3 u3 => wp_addi fun t4 u4 => ?_
  have c4 : Ctx L scr σ t4 := (c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)
  refine c4.wp_slot hg (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine wp_subm (B := L.B) (by rw [c5.st.sp]) (rS sDone c5 (by decide)) fun t6 u6 => ?_
  refine wp_mov fun t7 u7 => wp_subi fun t8 u8 c8 _ => wp_sbb_self c8 fun t9 u9 => ?_
  refine wp_and fun t10 u10 => wp_addi fun t11 u11 => wp_mov fun t12 u12 => WP.block_nil ?_
  have m12 : t12.mem = s.mem := by
    rw [u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hx : dl - c * g.H.D < 2 ^ 32 := by oomega
  have e6 : t6.gpr .ecx = BitVec.ofNat 32 (dl - c * g.H.D) := by
    rw [u6.gpr, u5.gpr, m5, u4.mem, u3.mem, u2.mem, u1.mem, hg.aFr ok sDone (by decide),
      P.dstL σ _ hm.1, hm.2.done, sub_ofNat (by omega)]
  refine ⟨((((((((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8 (by decide)
    (by decide)).upd u9 (by decide) (by decide)).upd u10 (by decide) (by decide)).upd u11 (by decide)
    (by decide)).upd u12 (by decide) (by decide))), by rw [m12]; exact ⟨hm, hd⟩, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.gpr, u1.gpr, u1.mem, hg.aFr ok sDone (by decide), P.dst σ _ hm.1,
      hm.2.done, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.gpr, u3.gpr, u2.other, u1.other, hc.ebp]
  · rw [u12.gpr, u11.gpr, u10.gpr, u9.gpr, u9.other .eax (by decide), u8.gpr, u7.gpr, e6,
      minSel hx (by omega)]

/-- The XOR of the digest into `dst`. -/
theorem mgfJ_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ (MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧
        s.gpr .edi = scr + BitVec.ofNat 32 (dOff + c * g.H.D) ∧ s.gpr .esi = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .ecx = BitVec.ofNat 32 (min g.H.D (dl - c * g.H.D)))
      (countLoop xorBody)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ DX g L scr so sl dOff dl c (dstv σ) (seed σ) s.mem) := by
  have hD := g.D_le
  have hD0 := g.D_pos
  have hfd := P.fd
  have hfs := P.fs
  have := P.do0; have := P.so0
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  generalize hn : min g.H.D (dl - c * g.H.D) = n
  have hn0 : 0 < n := by omega
  have hnD : n ≤ g.H.D := by omega
  have hnd : c * g.H.D + n ≤ dl := by omega
  refine (xor_vp hg (od := dOff + c * g.H.D) (os := oDig) (n := n) hn0 (by oomega) (by oomega) (by oomega)
    (X := fun σ m => MI g L scr so sl dOff dl c dstv seed Inv σ m ∧ Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) m)).mono
    (fun _ _ h => h) fun σ s ⟨hc, m₀, ⟨hm, hd⟩, hf, hx⟩ => ⟨hc, ?_, ?_, ?_, fun i hi => ?_, ?_⟩
  · refine P.I σ _ _ hm.1 (Frame.sub hf fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨sR scr dOff dl, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by oomega) (by rw [hg.F]; decide)) hm.2.ctr
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by oomega) (by rw [hg.F]; decide)) hm.2.done
  · have old := hm.2.dx i hi
    by_cases h1 : i < c * g.H.D
    · rw [ite_eq_left (by omega)]
      rw [ite_eq_left h1] at old
      rw [← old]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := scr) (o := dOff + i) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
    rw [ite_eq_right h1] at old
    by_cases h2 : i < c * g.H.D + n
    · rw [ite_eq_left (by omega), g.mask_byte (c := c) hi (by omega) (by omega), ← hd _ (by omega), ← old]
      have e := hx (i - c * g.H.D) (by omega)
      rw [show dOff + c * g.H.D + (i - c * g.H.D) = dOff + i by omega] at e
      exact e
    · rw [ite_eq_right (by omega), ← old]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := scr) (o := dOff + i) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
  · exact sbytes_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases P.sep with h | h
      · exact Geo.sep (by oomega) (by oomega) (by oomega)
      · exact Geo.sep (by oomega) (by oomega) (by oomega)) (by oomega) hm.2.sd

/-- The next counter and bytes masked. -/
theorem mgfK_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ DX g L scr so sl dOff dl c (dstv σ) (seed σ) s.mem)
      (.block (mgfNext g.H))
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl (c + 1) dstv seed Inv σ s.mem ∧
        s.cf = some (decide (c * g.H.D + g.H.D < dl))) := by
  have hD := g.D_le
  have hfd := P.fd
  have hfs := P.fs
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] g.certs.mgfNext (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, hm⟩ => ?_
  simp only [mgfNext, Impl.RsaPss.X86.ld, Impl.RsaPss.X86.st, Impl.RsaPss.X86.addi, Impl.RsaPkcs1Sig.X86.stk]
  refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => wp_addi fun t2 u2 => ?_
  refine (c1.upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 u3 => ?_
  refine c3.wp_slot hg (by decide) (by decide) (by decide) fun t4 c4 u4 => wp_addi fun t5 u5 => ?_
  refine (c4.upd u5 (by decide) (by decide)).wp_st hg (by decide) fun t6 c6 u6 => ?_
  refine wp_cmpm (B := L.B) (by rw [c6.st.sp]) (by rw [hg.aFr ok sDstLen (by decide)]; exact c6.rFr hg sDstLen (by decide))
    fun t7 u7 cf _ => WP.block_nil ?_
  have e2 : t2.gpr .eax = BitVec.ofNat 32 (c + 1) := by rw [u2.gpr, u1.gpr, hm.ctr, BitVec.ofNat_add_ofNat]
  have m3 : t3.mem = s.mem.writeW (L.fr sCtr) (BitVec.ofNat 32 (c + 1)) := by rw [u3.mem, e2, u2.mem, u1.mem]
  have e5 : t5.gpr .eax = BitVec.ofNat 32 (c * g.H.D + g.H.D) := by
    rw [u5.gpr, u4.gpr, m3, Lay.readW_fr_other (d := sDone) (e := sCtr) L _ _ (by decide) (by decide)
      (by decide), hm.done, BitVec.ofNat_add_ofNat]
  have m7 : t7.mem = (s.mem.writeW (L.fr sCtr) (BitVec.ofNat 32 (c + 1))).writeW (L.fr sDone)
      (BitVec.ofNat 32 (c * g.H.D + g.H.D)) := by rw [u7.mem, u6.mem, e5, u5.mem, u4.mem, m3]
  have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t7.mem := by
    rw [m7]
    exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
  have dis : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
    intro r hr o n hon
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  rw [u6.gpr, e5, u6.mem, e5, u5.mem, u4.mem, m3, hg.aFr ok sDstLen (by decide),
    Lay.readW_fr_other (d := sDstLen) (e := sDone) L _ _ (by decide) (by decide) (by decide),
    Lay.readW_fr_other (d := sDstLen) (e := sCtr) L _ _ (by decide) (by decide) (by decide), P.dstL σ _ hi,
    toNat_ofNat_lt (by oomega), toNat_ofNat_lt (by oomega)] at cf
  refine ⟨c6.fupd u7, ⟨P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, ?_, ?_⟩⟩, cf⟩
  · rw [m7, Lay.readW_fr_other (d := sCtr) (e := sDone) L _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m7, Mem.readW_writeW_self32, Nat.succ_mul]
  · intro i hi'
    rw [Nat.succ_mul]
    exact sbytes_keep fr (fun r hr => dis r hr _ _ (by oomega)) (by oomega) hm.dx i hi'
  · exact sbytes_keep fr (fun r hr => dis r hr _ _ (by oomega)) (by oomega) hm.sd

/-- An iteration of `mgfXor`. -/
theorem mgfIter_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem)
      (mgfRound g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl (c + 1) dstv seed Inv σ s.mem ∧
        s.cf = some (decide (c * g.H.D + g.H.D < dl))) := by
  have hc32 : c < 2 ^ 32 := by
    have := P.fd
    have : c ≤ c * g.H.D := Nat.le_mul_of_pos_right c g.D_pos
    oomega
  show VP _ (.seq (.block initArgs) (.seq (callInit g.H) (.seq (.block updSrcArgs) (.seq (callUpd g.H)
    (.seq (.block ctrSet) (.seq (.block updCtrArgs) (.seq (callUpd g.H) (.seq (.block finArgs)
      (.seq (callFin g.H) (.seq (.block (xorSet g.H)) (.seq (countLoop xorBody)
        (.block (mgfNext g.H))))))))))))) _
  exact vpAssoc (VP.seq (mgfA_vp P c) (VP.seq (mgfB_vp P c) (VP.seq (mgfC_vp P c) (VP.seq (mgfD_vp P c hc32)
    (VP.seq (mgfE_vp P c) (VP.seq (mgfF_vp P c) (VP.seq (mgfG_vp P c) (VP.seq (mgfH_vp P c)
      (VP.seq (mgfI_vp P c hcd) (VP.seq (mgfJ_vp P c hcd) (mgfK_vp P c hcd)))))))))))

end Iter

/-- `dst ⊕= MGF1(src, dl)`. -/
theorem mgf_vp (P : MP g L scr so sl dOff dl seed Inv) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ (∀ i < dl, s.mem (sa scr (dOff + i)) = dstv σ i) ∧
        ∀ i < sl, s.mem (sa scr (so + i)) = (seed σ).getD i 0)
      (mgfXor g.H)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧
        (∀ i < dl, s.mem (sa scr (dOff + i)) = dstv σ i ^^^ (Spec.Mgf1.mgf1 g.G (seed σ) dl).getD i 0) ∧
        ∀ i < sl, s.mem (sa scr (so + i)) = (seed σ).getD i 0) := by
  have hD := g.D_le
  have hD0 := g.D_pos
  have hfd := P.fd
  have hfs := P.fs
  have hdl := P.dl0
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  generalize hK : (dl + g.H.D - 1) / g.H.D = K
  have hK0 : 0 < K := by
    rw [← hK]; exact (Nat.le_div_iff_mul_le hD0).2 (by omega)
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl 0 dstv seed Inv σ s.mem)
    (VP.taint [.esp, .ebp] mgfInit_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, hd, hs⟩ => ?_) ?_
  · simp only [mgfInit, Impl.RsaPss.X86.mi, Impl.RsaPss.X86.st]
    refine wp_movi fun t1 u1 => (hc.upd u1 (by decide) (by decide)).wp_st hg (by decide) fun t2 c2 u2 =>
      c2.wp_st hg (by decide) fun t3 c3 u3 => WP.block_nil ?_
    have m3 : t3.mem = (s.mem.writeW (L.fr sCtr) (0 : BitVec 32)).writeW (L.fr sDone) (0 : BitVec 32) := by
      rw [u3.mem, u2.gpr, u2.mem, u1.mem, u1.gpr]; rfl
    have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t3.mem := by
      rw [m3]
      exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
    have dis : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
      intro r hr o n hon
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
      · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    refine ⟨c3, P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, fun i hi' => ?_, ?_⟩⟩
    · rw [m3, Lay.readW_fr_other (d := sCtr) (e := sDone) L _ _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]; rfl
    · rw [m3, Mem.readW_writeW_self32, Nat.zero_mul]; rfl
    · rw [ite_eq_right (by omega)]
      exact sbytes_keep fr (fun r hr => dis r hr _ _ (by oomega)) (by oomega) hd i hi'
    · exact sbytes_keep fr (fun r hr => dis r hr _ _ (by oomega)) (by oomega) hs
  refine (VP.loop (I := fun k σ s => k ≤ K ∧ Ctx L scr σ s ∧ MI g L scr so sl dOff dl (K - k) dstv seed Inv σ s.mem)
    (fun k => ?_) (K - 1)).mono (fun σ s hs => ⟨by omega, by rw [show K - (K - 1 + 1) = 0 by omega]; exact hs⟩)
    fun _ _ h => h
  by_cases hk : k + 1 ≤ K
  swap
  · exact VP.empty fun σ s ⟨h, _⟩ => hk h
  generalize hc : K - (k + 1) = c
  have key : ∀ x, (dl + g.H.D - 1) / g.H.D ≤ x + 1 ↔ dl ≤ x * g.H.D + g.H.D := fun x => by
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hD0, Nat.succ_mul, Nat.succ_mul]
    omega
  have hcd : c * g.H.D < dl := by
    have := (Nat.le_div_iff_mul_le hD0).1 (show c + 1 ≤ (dl + g.H.D - 1) / g.H.D by omega)
    rw [Nat.succ_mul] at this
    omega
  refine (mgfIter_vp P c hcd).mono (fun σ s ⟨_, hs⟩ => hs) fun σ s ⟨hc', hm, z⟩ => ⟨?_, fun h0 => ?_, fun hp => ?_⟩
  · show eval .b s = _
    simp only [eval, z]
    have e := key c
    rw [hK] at e
    by_cases hz : k = 0
    · rw [decide_eq_false (fun h' => by have := e.2 (by omega); omega), hz]; rfl
    · rw [decide_eq_true (by by_contra h'; have := e.2 (by omega); omega), decide_eq_true (by omega)]
  · have e := (key c).1 (by omega)
    refine ⟨hc', hm.1, fun i hi => ?_, hm.2.sd⟩
    rw [hm.2.dx i hi, ite_eq_left (by rw [Nat.succ_mul]; omega)]
  · exact ⟨by omega, hc', by rw [show K - k = c + 1 by omega]; exact hm⟩

end VG.Proof.RsaOaep.X86
