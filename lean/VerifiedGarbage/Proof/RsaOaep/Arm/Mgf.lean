module

public import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
public import VerifiedGarbage.Proof.RsaPss.Arm.CtMgf
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgfLoop
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.Mgf1.Bytes
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPss.MgfBytes

/-!
# RSAES-OAEP on ARMv7: `dst ⊕= MGF1(src, dstLen)`

`OHash`: a hash function as RSAES-OAEP on ARMv7 uses it, its streaming
functions verified (`Pbkdf2.Stream.Arm.HashOK`) and the hash function as
RSA's padding takes it; from the RSASSA-PSS one (`OHash.ofPss`).

`mgf_vp`: with `src` (`sl` bytes at `so`) and `dst` (`dl` bytes at `dOff`)
in `EM`'s place in our part of `scratch`, their addresses and lengths in
their slots, `mgfXor` XORs MGF1's mask of `src` into `dst`, one digest of
`src ‖ C` (by the streaming `init`, two `update`s and `finalize`) at a time.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa countLoop sCtr sDone ctrPut xorBody mgfInit)
open VG.Impl.Pbkdf2.Stream.Arm (Hash)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-- A hash function, as RSAES-OAEP on ARMv7 uses it. -/
structure OHash where
  H : Hash
  ok : HashOK H
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  glen : G.len = H.D
  valid : Proof.Mgf1.Valid G

/-- The RSASSA-PSS hash function's streaming functions. -/
def OHash.ofPss (h : PssHash) : OHash := ⟨h.H.md.st, h.ok.stream, h.G, h.hash, h.glen, h.valid⟩

namespace OHash

variable (g : OHash)

theorem D_pos : 0 < g.H.D := g.ok.hD0
theorem D_le : g.H.D ≤ 64 := by have := g.ok.hDF; have := g.ok.hF; omega
theorem DF : g.H.D ≤ g.H.F := g.ok.hDF
theorem F_le : g.H.F ≤ 64 := g.ok.hF
theorem S_le : g.H.S ≤ 256 := g.ok.hSB
theorem Wb_le : g.ok.Wb ≤ 512 := by have := g.ok.hWb; have := g.ok.hW; omega

/-- A byte of the mask, in the digest of `src ‖ C` for the counter `c`. -/
theorem mask_byte {seed : List Byte} {dl c i : Nat} (hi : i < dl) (h₁ : c * g.H.D ≤ i) (h₂ : i < c * g.H.D + g.H.D) :
    (Spec.Mgf1.mgf1 g.G seed dl).getD i 0 = (g.ok.SH.H.hash (seed ++ Spec.Rsa.i2osp c 4)).getD (i - c * g.H.D) 0 := by
  have hD0 := g.D_pos
  rw [Proof.Mgf1.mgf1_getD g.valid _ hi, g.glen, ← g.hash]
  have e1 : i / g.H.D = c := Nat.div_eq_of_lt_le h₁ (by rw [Nat.succ_mul]; omega)
  have e2 : i % g.H.D = i - c * g.H.D := by
    have := Nat.mod_add_div i g.H.D
    rw [e1, Nat.mul_comm] at this
    omega
  rw [e1, e2]

end OHash

variable {L : Lay} {scr : BitVec 32} (g : OHash)

/-- The bytes at `scr + o` as a list. -/
theorem bytesAt_scr (hg : Geo L scr) {m : Mem} {o n : Nat} (h : o + n ≤ oRsa) {xs : List Byte} (hl : xs.length = n)
    (hx : ∀ i < n, m (sa scr (o + i)) = xs.getD i 0) :
    Spec.Sha256.bytesAt m (State.addr (scr + BitVec.ofNat 32 o)) n = xs := by
  apply List.ext_getElem (by simp [Spec.Sha256.bytesAt, hl])
  intro i h1 h2
  simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Sha256.bytesAt, List.getElem_map, List.getElem_range]
  have e := hx i h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at e
  rw [← e]
  by_cases hn : n = 0
  · omega
  rw [hg.addr (by omega), sa, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-! ## The parameters -/

/-- What `mgfXor` writes. -/
abbrev mgfW (L : Lay) (scr : BitVec 32) (dOff dl : Nat) : List Region :=
  [sR scr oSt g.H.S, sR scr oCtr 4, sR scr oDig g.H.F, sR scr oW g.ok.Wb, L.LOW, sR scr dOff dl, slotR L sCtr,
    slotR L sDone]

/-- The parameters of `mgfXor`: `src` (`sl` bytes at `so`) and `dst` (`dl`
bytes at `dOff`), apart, in `EM`'s place; their slots, and what the caller
keeps (`Inv`). -/
structure MP (L : Lay) (scr : BitVec 32) (so sl dOff dl : Nat) (seed : State → List Byte)
    (Inv : State → Mem → Prop) : Prop where
  hg : Geo L scr
  sl0 : 0 < sl
  dl0 : 0 < dl
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

/-- A range of our part of `scratch` from `oSt` on misses them. -/
theorem away_hi {o n : Nat} (ho : oSt ≤ o) (hn : o + n ≤ oRsa) : Away L scr so sl dOff dl (sR scr o n) := by
  have := P.fs; have := P.fd
  obtain ⟨σ', ok⟩ := P.hg.ok
  exact ⟨P.hg.slot ok hn (by rw [P.hg.F]; decide), P.hg.slot ok hn (by rw [P.hg.F]; decide),
    Geo.sep (by oomega) (by oomega) hn, Geo.sep (by oomega) (by oomega) hn⟩

theorem away_low : Away L scr so sl dOff dl L.LOW := by
  have := P.fs; have := P.fd
  obtain ⟨σ', ok⟩ := P.hg.ok
  exact ⟨Lay.fr_low (by decide) (by have := ok.B56; have := L.B.isLt; omega),
    Lay.fr_low (by decide) (by have := ok.B56; have := L.B.isLt; omega), P.hg.low ok (by oomega),
    P.hg.low ok (by oomega)⟩

/-- So does a slot other than theirs. -/
theorem away_slot {d : Nat} (hd : d + 4 ≤ frameBytes) (h₁ : d + 4 ≤ sCtr ∨ sDone + 4 ≤ d) :
    Away L scr so sl dOff dl (slotR L d) := by
  have := P.fs; have := P.fd
  obtain ⟨σ', ok⟩ := P.hg.ok
  have hF : d + 4 ≤ L.F + 56 := by rw [P.hg.F]; unfold frameBytes at hd ⊢; omega
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
      (.seq (.block initArgs) (.call g.H.initN g.H.initC))
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) []) := by
  have := g.S_le
  refine init_vp P.hg g.H g.ok (Inv := MI g L scr so sl dOff dl c dstv seed Inv) fun σ m m' hm hf =>
    P.keep hm hf (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_low

/-- `update(state, 0, src, sl, work)`'s arguments. -/
theorem mgfB_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [])
      (.block updSrcArgs)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
        Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 so)) sl = seed σ ∧
        UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s) := by
  have hg := P.hg
  have := P.fs
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, rp⟩ => ?_
  have hw : WP isa (.block updSrcArgs) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      UArgs scr (scr + BitVec.ofNat 32 so) sl 0 t := by
    prun [updSrcArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, P.src σ _ hm.1, P.srcL σ _ hm.1,
      sSrc_lt, sSrcLen_lt, movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oW < 2 ^ 16 by decide)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine WP.mono hw fun t ⟨m, rd, wr, sp, u⟩ => ⟨hc.regs rd wr sp m, m ▸ hm, m ▸ rp, rfl, ?_, u⟩
  rw [m]; exact bytesAt_scr hg (by oomega) (P.sd σ) hm.2.sd

/-- `update` absorbs `src`. -/
theorem mgfC_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
        Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 so)) sl = seed σ ∧
        UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s)
      (updCall g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) := by
  have hg := P.hg
  have := P.fs; have := g.S_le; have := g.Wb_le
  obtain ⟨σ', ok⟩ := hg.ok
  have aS : State.addr (scr + BitVec.ofNat 32 so) = sa scr so := hg.addr (by have := P.sl0; oomega)
  refine upd_vp hg g.H g.ok (msg := fun _ => []) (dat := seed) (c := 0) (Inv := MI g L scr so sl dOff dl c dstv seed Inv)
    (hg.rbuf (o := so) (n := sl) (by oomega) P.sl0)
    (by rw [aS]; exact Geo.sep (by oomega) (by oomega) (by oomega))
    (by rw [aS]; exact Geo.sep (by oomega) (by oomega) (by oomega)) (by rw [aS]; exact hg.low ok (by oomega))
    (by decide) fun σ m m' hm hf => P.keep hm hf (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_low

/-- The counter, big-endian, at `oCtr`. -/
theorem mgfD_vp (hc32 : c < 2 ^ 32) :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ))
      (.seq (.block ctrSet) (.block ctrPut))
      (fun σ s => Ctx L scr σ s ∧ (MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧ Cb scr c s.mem) := by
  have hg := P.hg
  have := P.fs; have := g.S_le
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ (MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
      g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧
      s.gpr .r0 = scr + BitVec.ofNat 32 oCtr ∧ s.gpr .r1 = BitVec.ofNat 32 c)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, rp⟩ => ?_)
    (VP.taint _ ctrPut_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, ⟨hm, rp⟩, r0, r1⟩ => ?_)
  · have hw : WP isa (.block ctrSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = scr + BitVec.ofNat 32 oCtr ∧ t.gpr .r1 = BitVec.ofNat 32 c := by
      prun [ctrSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hm.2.ctr,
        movw_val (show oCtr < 2 ^ 16 by decide)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1⟩ => ⟨hc.regs rd wr sp m, ⟨m ▸ hm, m ▸ rp⟩, r0, r1⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  · have a0 : State.addr (scr + BitVec.ofNat 32 oCtr) = sa scr oCtr := hg.addr (by oomega)
    have aj : ∀ j, j < 4 → State.addr (scr + BitVec.ofNat 32 (oCtr + j)) = sa scr (oCtr + j) :=
      fun j hj => hg.addr (by oomega)
    have wj : ∀ j, j < 4 → InRegions s.wr (sa scr (oCtr + j)) 1 := fun j hj => hg.wr hc.st (by oomega)
    have w0 : InRegions s.wr (sa scr oCtr) 1 := hg.wr hc.st (by oomega)
    have hw : WP isa (.block ctrPut) s fun t =>
        t.mem = (((s.mem.writeW (sa scr oCtr) (BitVec.ofNat 8 (c / 256 ^ 3))).writeW (sa scr (oCtr + 1))
          (BitVec.ofNat 8 (c / 256 ^ 2))).writeW (sa scr (oCtr + 2)) (BitVec.ofNat 8 (c / 256 ^ 1))).writeW
            (sa scr (oCtr + 3)) (BitVec.ofNat 8 (c / 256 ^ 0)) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [ctrPut, r0, r1, a0, aj 1 (by decide), aj 2 (by decide), aj 3 (by decide), w0, wj 1 (by decide),
        wj 2 (by decide), wj 3 (by decide), shrByte hc32 3, shrByte hc32 2, shrByte hc32 1, shr0 c,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [sR scr oCtr 4] s.mem t.mem := by
      rw [m]
      refine (((frame_byte scr _ _ ?_ ?_ ?_).trans (frame_byte scr _ _ ?_ ?_ ?_)).trans
        (frame_byte scr _ _ ?_ ?_ ?_)).trans (frame_byte scr _ _ ?_ ?_ ?_) <;> oomega
    refine ⟨ctxW hg hc fr (fun r hr => .inl ⟨oCtr, 4, by oomega, by simpa using hr⟩) rd wr sp,
      ⟨P.keep hm fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact P.away_hi (by oomega) (by oomega),
        g.ok.repr _ _ _ _ _ (fun i hi => ?_) rp⟩, fun i hi => ?_⟩
    · exact fr.bytes (R := sR scr oSt g.H.S) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by oomega) (by oomega) (by oomega))
        (by show g.H.S ≤ 2 ^ 64; omega) hi
    rw [m, sa_write scr _ _ (o := oCtr + 3) (i := oCtr + i) (by oomega) (by oomega),
      sa_write scr _ _ (o := oCtr + 2) (i := oCtr + i) (by oomega) (by oomega),
      sa_write scr _ _ (o := oCtr + 1) (i := oCtr + i) (by oomega) (by oomega),
      sa_write scr _ _ (o := oCtr) (i := oCtr + i) (by oomega) (by oomega), i2osp4_getD c _ hi]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, Nat.reduceSub]

/-- `update(state, sl, scratch + oCtr, 4, work)`'s arguments. -/
theorem mgfE_vp :
    VP (fun σ s => Ctx L scr σ s ∧ (MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧ Cb scr c s.mem)
      (.block updCtrArgs)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
        Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 oCtr)) 4 = Spec.Rsa.i2osp c 4 ∧
        UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s) := by
  have hg := P.hg
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, ⟨hm, rp⟩, cb⟩ => ?_
  have hw : WP isa (.block updCtrArgs) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl t := by
    prun [updCtrArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, P.srcL σ _ hm.1, sSrcLen_lt,
      movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oW < 2 ^ 16 by decide),
      movw_val (show oCtr < 2 ^ 16 by decide), movw_val (show 4 < 2 ^ 16 by decide)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine WP.mono hw fun t ⟨m, rd, wr, sp, u⟩ => ⟨hc.regs rd wr sp m, m ▸ hm, m ▸ rp,
    by rw [List.nil_append, P.sd σ], ?_, u⟩
  rw [m]; exact bytesAt_scr hg (by oomega) (i2osp4_length c) cb

/-- `update` absorbs the counter. -/
theorem mgfF_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
        Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 oCtr)) 4 = Spec.Rsa.i2osp c 4 ∧
        UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s)
      (updCall g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4)) := by
  have hg := P.hg
  have := P.fs; have := g.S_le; have := g.Wb_le
  obtain ⟨σ', ok⟩ := hg.ok
  have aC : State.addr (scr + BitVec.ofNat 32 oCtr) = sa scr oCtr := hg.addr (by oomega)
  refine upd_vp hg g.H g.ok (msg := fun σ => [] ++ seed σ) (dat := fun _ => Spec.Rsa.i2osp c 4) (c := sl)
    (Inv := MI g L scr so sl dOff dl c dstv seed Inv) (hg.rbuf (o := oCtr) (n := 4) (by oomega) (by decide))
    (by rw [aC]; exact Geo.sep (by oomega) (by oomega) (by oomega))
    (by rw [aC]; exact Geo.sep (by oomega) (by oomega) (by oomega)) (by rw [aC]; exact hg.low ok (by oomega))
    (by oomega) fun σ m m' hm hf => P.keep hm hf (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_low

/-- `finalize(state, sl + 4, scratch + oDig, work)`'s arguments, the working
space moved to `r12`. -/
theorem mgfG_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4))
      (.seq (.block finArgs) (.block toR12))
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
        ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s) := by
  have hg := P.hg
  have := P.fs
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
      g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4)) ∧
      s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ s.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
      s.gpr .r10 = scr + BitVec.ofNat 32 oW ∧ s.gpr .r2 = BitVec.ofNat 32 (sl + 4) ∧ s.gpr .r3 = 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, rp⟩ => ?_)
    ((toR12_vp (fun σ s h => h.2.2.2.1) fun σ s v h => ?_).mono
      (fun _ _ h => h) fun σ s ⟨⟨⟨hc, hm, rp⟩, r0, r1, _, r2, r3⟩, r12⟩ => ⟨hc, hm, rp,
        by rw [List.length_append, List.nil_append, P.sd σ, i2osp4_length], r0, r1, r12, r2, r3⟩)
  · have e4 : BitVec.ofNat 32 sl + 4 = BitVec.ofNat 32 (sl + 4) := by
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.ofNat_add_ofNat]
    have hw : WP isa (.block finArgs) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ t.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
        t.gpr .r10 = scr + BitVec.ofNat 32 oW ∧ t.gpr .r2 = BitVec.ofNat 32 (sl + 4) ∧ t.gpr .r3 = 0 := by
      prun [finArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, P.srcL σ _ hm.1, sSrcLen_lt,
        movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oW < 2 ^ 16 by decide),
        movw_val (show oDig < 2 ^ 16 by decide), BitVec.ofNat_add_ofNat, dpVal, e4]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, r10, r2, r3⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hm, m ▸ rp⟩, r0, r1, r10,
      r2, r3⟩
  · obtain ⟨⟨hc, hm, rp⟩, r0, r1, r10, r2, r3⟩ := h
    have e : ∀ r, r ≠ .r12 → (s.setReg .r12 v).gpr r = s.gpr r := fun r hr => by
      simp only [VG.Arm.RegUpd.gpr_setReg, hr, ite_false]
    exact ⟨⟨Ctx.setReg_iff.mpr hc, hm, rp⟩, by rw [e _ (by decide), r0], by rw [e _ (by decide), r1],
      by rw [e _ (by decide), r10], by rw [e _ (by decide), r2], by rw [e _ (by decide), r3]⟩

/-- `finalize` writes the digest. -/
theorem mgfH_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
        ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s)
      (finCall g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) := by
  have hg := P.hg
  have := P.fs; have := g.S_le; have := g.Wb_le; have := g.F_le; have := g.DF
  refine (fin_vp hg g.H g.ok (o := oDig) (c := sl + 4) (msg := fun σ => [] ++ seed σ ++ Spec.Rsa.i2osp c 4)
    (Inv := MI g L scr so sl dOff dl c dstv seed Inv)
    (.inr (by oomega)) (.inl (by oomega)) (by oomega) (by oomega) fun σ m m' hm hf => P.keep hm hf (fun r hr => ?_) fun r hr => ?_).mono
    (fun _ _ h => h) fun σ s ⟨hc, hm, hd⟩ => ⟨hc, hm, fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_hi (by oomega) (by oomega)
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
        s.gpr .r0 = scr + BitVec.ofNat 32 (dOff + c * g.H.D) ∧ s.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .lr = BitVec.ofNat 32 (min g.H.D (dl - c * g.H.D))) := by
  have hD := g.D_le
  have hfd := P.fd
  have hg := P.hg
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, hd⟩ => ?_
  have hw : WP isa (.block (xorSet g.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (dOff + c * g.H.D) ∧
      t.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
      t.gpr .lr = if dl - c * g.H.D < g.H.D then BitVec.ofNat 32 (dl - c * g.H.D) else BitVec.ofNat 32 g.H.D := by
    prun [xorSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, P.dst σ _ hm.1,
      P.dstL σ _ hm.1, hm.2.done, sDst_lt, sDstLen_lt, movw_val (show oDig < 2 ^ 16 by decide),
      movw_val (show g.H.D < 2 ^ 16 by omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      Offset.ofNat_sub_ofNat (w := 32) (show c * g.H.D ≤ dl by omega),
      ltBit (a := dl - c * g.H.D) (b := g.H.D) (by oomega) (by omega), neg_bit, neg_bit', selW, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨hc.regs rd wr sp m, m ▸ ⟨hm, hd⟩, r0, r1, ?_⟩
  rw [lr]
  split
  · rw [Nat.min_eq_right (by omega)]
  · rw [Nat.min_eq_left (by omega)]

/-- The XOR of the digest into `dst`. -/
theorem mgfJ_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ (MI g L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧
        s.gpr .r0 = scr + BitVec.ofNat 32 (dOff + c * g.H.D) ∧ s.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .lr = BitVec.ofNat 32 (min g.H.D (dl - c * g.H.D)))
      (countLoop xorBody)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ DX g L scr so sl dOff dl c (dstv σ) (seed σ) s.mem) := by
  have hD := g.D_le
  have hD0 := g.D_pos
  have hfd := P.fd
  have hfs := P.fs
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
        s.z = decide (dl ≤ c * g.H.D + g.H.D)) := by
  have hD := g.D_le
  have hfd := P.fd
  have hfs := P.fs
  have hg := P.hg
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hm⟩ => ?_
  have r1 : ∀ v : BitVec 32, (s.mem.writeW (L.fr sCtr) v).readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * g.H.D) :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide), hm.done]
  have r2 : ∀ v w : BitVec 32, ((s.mem.writeW (L.fr sCtr) v).writeW (L.fr sDone) w).readW (L.fr sDstLen) 32 =
      BitVec.ofNat 32 dl :=
    fun v w => by rw [slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      P.dstL σ _ hi]
  have hw : WP isa (.block (mgfNext g.H)) s fun t =>
      t.mem = (s.mem.writeW (L.fr sCtr) (BitVec.ofNat 32 (c + 1))).writeW (L.fr sDone)
        (BitVec.ofNat 32 (c * g.H.D + g.H.D)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.z = decide (dl ≤ c * g.H.D + g.H.D) := by
    prun [mgfNext, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hm.ctr, r1, r2, sDstLen_lt,
      movw_val (show g.H.D < 2 ^ 16 by omega), VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32,
      BitVec.ofNat_add_ofNat, ltBit (a := c * g.H.D + g.H.D) (b := dl) (by oomega) (by oomega), bit_z, dpVal]
    simp only [decide_eq_decide]
    omega
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ?_
  have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t.mem := by
    rw [m]
    exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
  obtain ⟨σ', ok⟩ := hg.ok
  have dis : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
    intro r hr o n hon
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
    ⟨P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, ?_, ?_⟩⟩, z⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slotW hg (by decide)
    · exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slotSep (by decide) (by decide) (by decide)
    · exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32, Nat.succ_mul]
  · intro i hi'
    rw [Nat.succ_mul]
    exact sbytes_keep fr (fun r hr => dis r hr _ _ (by oomega)) (by oomega) hm.dx i hi'
  · exact sbytes_keep fr (fun r hr => dis r hr _ _ (by oomega)) (by oomega) hm.sd

/-- An iteration of `mgfXor`. -/
theorem mgfIter_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl c dstv seed Inv σ s.mem)
      (mgfRound g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g L scr so sl dOff dl (c + 1) dstv seed Inv σ s.mem ∧
        s.z = decide (dl ≤ c * g.H.D + g.H.D)) := by
  have hc32 : c < 2 ^ 32 := by
    have := P.fd
    have : c ≤ c * g.H.D := Nat.le_mul_of_pos_right c g.D_pos
    oomega
  show VP _ (.seq (.block initArgs) (.seq (.call g.H.initN g.H.initC) (.seq (.block updSrcArgs) (.seq (updCall g.H)
    (.seq (.block ctrSet) (.seq (.block ctrPut) (.seq (.block updCtrArgs) (.seq (updCall g.H) (.seq (.block finArgs)
      (.seq (.block toR12) (.seq (finCall g.H) (.seq (.block (xorSet g.H)) (.seq (countLoop xorBody)
        (.block (mgfNext g.H))))))))))))))) _
  exact VP.assoc (VP.seq (mgfA_vp P c) (VP.seq (mgfB_vp P c) (VP.seq (mgfC_vp P c) (VP.assoc (VP.seq (mgfD_vp P c hc32)
    (VP.seq (mgfE_vp P c) (VP.seq (mgfF_vp P c) (VP.assoc (VP.seq (mgfG_vp P c) (VP.seq (mgfH_vp P c)
      (VP.seq (mgfI_vp P c hcd) (VP.seq (mgfJ_vp P c hcd) (mgfK_vp P c hcd)))))))))))))

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
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hd, hs⟩ => ?_) ?_
  · have hw : WP isa (.block mgfInit) s fun t =>
        t.mem = (s.mem.writeW (L.fr sCtr) (0 : BitVec 32)).writeW (L.fr sDone) (0 : BitVec 32) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [mgfInit, sp0, st, mw, hc.st.sp, hc.aFr hg, hc.wFr hg]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t.mem := by
      rw [m]
      exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
    have dis : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
      intro r hr o n hon
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
      · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
      P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, fun i hi' => ?_, ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotW hg (by decide)
      · exact slotW hg (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotSep (by decide) (by decide) (by decide)
      · exact slotSep (by decide) (by decide) (by decide)
    · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
    · rw [m, Mem.readW_writeW_self32, Nat.zero_mul]; rfl
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
  · rw [VG.Proof.X25519.Arm.eval_ne, z]
    have e := key c
    rw [hK] at e
    by_cases hz : k = 0
    · rw [decide_eq_true (e.1 (by omega)), hz]; rfl
    · rw [decide_eq_false (fun h' => hz (by have := e.2 h'; omega))]
      simp only [Bool.not_false, Option.some.injEq]
      exact (decide_eq_true (by omega)).symm
  · have e := (key c).1 (by omega)
    refine ⟨hc', hm.1, fun i hi => ?_, hm.2.sd⟩
    rw [hm.2.dx i hi, ite_eq_left (by rw [Nat.succ_mul]; omega)]
  · exact ⟨by omega, hc', by rw [show K - k = c + 1 by omega]; exact hm⟩

end VG.Proof.RsaOaep.Arm
