module

public import VerifiedGarbage.Proof.RsaPss.X86.CtHash
public import VerifiedGarbage.Proof.RsaPss.X86.CtSel
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86.SseDword

/-!
# RSASSA-PSS on x86: the stages of an iteration of `DB ⊕= MGF1(H, dbLen)`

With `DB` at `oEm + lo` (`dbLen` bytes, both in their slots) and the seed
`H` after it, an iteration of `mgfXor` clears `Y`'s first block
(`mgfA_vp`), copies the seed to it (`mgfB_vp`), puts the counter after it
(`mgfC_vp`) and hashes `H ‖ C` in one block with `ctHash`; the rest is in
`CtMgfLoop`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The hash function as MGF1 takes it has digests of `hLen` bytes. -/
theorem PssHash.valid : Proof.Mgf1.Valid h.G := by
  refine ⟨by rw [h.glen]; exact h.D_pos, fun x => ?_⟩
  rw [h.hash, h.ok.link.hash, List.length_take, Md.hash, h.md.digest_length, h.glen]
  exact Nat.min_eq_left h.D_le

/-- A slot is in what the body may write. -/
theorem slotW (hg : Geo L scr) {d : Nat} (hd : d + 4 ≤ frameBytes) : ∃ R ∈ L.W, Region.Sub (slotR L d) R :=
  ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; exact hd)⟩

/-- Two slots apart. -/
theorem slotSep {d e : Nat} (hd : d + 4 ≤ frameBytes) (he : e + 4 ≤ frameBytes) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (slotR L d).Disjoint (slotR L e) :=
  Lay.fr_sep h (by unfold frameBytes at hd; omega) (by unfold frameBytes at he; omega)

/-- A slot other than `sLb` and `sBi` misses what `ctHash` writes. -/
theorem ctW_slot (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (hb : d + 4 ≤ sBi ∨ sBi + 4 ≤ d) (hl : d + 4 ≤ sLb ∨ sLb + 4 ≤ d) :
    ∀ r ∈ ctW h L scr T, (slotR L d).Disjoint r := by
  have hN := h.N_le
  have hB := h.B_le
  have hso := h.so_le
  obtain ⟨σ', ok⟩ := hg.ok
  have hF : d + 4 ≤ L.F + 16 := by rw [hg.F]; omega
  have hC : L.C ≤ 2 ^ 32 := by have := ok.BC; have := L.B.isLt; omega
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg.slot ok (by pomega) hF
  · exact Lay.fr_low (by unfold frameBytes at hd; omega) hC
  · exact hg.slot ok (by pomega) hF
  · exact slotSep hd (by decide) hl
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact slotSep hd (by decide) hb
  · exact hg.slot ok (by pomega) hF

/-- A range of `EM`'s place misses what `ctHash` writes. -/
theorem ctW_em (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) {o n : Nat} (h₁ : oEm ≤ o) (h₂ : o + n ≤ oY) :
    ∀ r ∈ ctW h L scr T, (sR scr o n).Disjoint r := by
  have hN := h.N_le
  have hB := h.B_le
  have hso := h.so_le
  obtain ⟨σ', ok⟩ := hg.ok
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact hg.low ok (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
  · exact Geo.sep (by pomega) (by pomega) (by pomega)

/-- What `mgfXor` writes. -/
abbrev mgfW (L : Lay) (scr : BitVec 32) (lo db : Nat) : List Region :=
  ctW h L scr h.B ++ [sR scr (oEm + lo) db, slotR L sCtr, slotR L sDone, slotR L sL, slotR L sNb]

/-- The memory before iteration `c` of `mgfXor`: the counter, the bytes
masked, `DB` masked up to `c hLen` bytes, and the seed. -/
structure MB (L : Lay) (scr : BitVec 32) (lo db c : Nat) (dbv : Nat → Byte) (seed : List Byte) (m : Mem) : Prop where
  ctr : m.readW (L.fr sCtr) 32 = BitVec.ofNat 32 c
  done : m.readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * h.D)
  dbx : ∀ i < db, m (sa scr (oEm + lo + i)) =
    if i < c * h.D then dbv i ^^^ (Spec.Mgf1.mgf1 h.G seed db).getD i 0 else dbv i
  sd : ∀ i < h.D, m (sa scr (oEm + lo + db + i)) = seed.getD i 0

theorem MB.keep {lo db c : Nat} {dbv : Nat → Byte} {seed : List Byte} {m m' : Mem} {rs : List Region}
    (hm : MB h L scr lo db c dbv seed m) (hf : Frame rs m m') (hn : oEm + lo + db + h.D < 2 ^ 64)
    (hs : ∀ r ∈ rs, (slotR L sCtr).Disjoint r ∧ (slotR L sDone).Disjoint r ∧
      (sR scr (oEm + lo) db).Disjoint r ∧ (sR scr (oEm + lo + db) h.D).Disjoint r) :
    MB h L scr lo db c dbv seed m' :=
  ⟨slot_keep hf (fun r hr => (hs r hr).1) hm.ctr, slot_keep hf (fun r hr => (hs r hr).2.1) hm.done,
    sbytes_keep hf (fun r hr => (hs r hr).2.2.1) (by omega) hm.dbx,
    sbytes_keep hf (fun r hr => (hs r hr).2.2.2) (by omega) hm.sd⟩

/-- The counter's bytes. -/
theorem i2osp4_getD (c j : Nat) (hj : j < 4) :
    (Spec.Rsa.i2osp c 4).getD j 0 = BitVec.ofNat 8 (c / 256 ^ (3 - j)) := by
  simp [Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, hj]

theorem i2osp4_length (c : Nat) : (Spec.Rsa.i2osp c 4).length = 4 := by simp [Spec.Rsa.i2osp]

/-- Bit `8k + j` of a word with its bytes reversed. -/
theorem bswap_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first | omega | (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

/-- Byte `k` of the counter, big-endian. -/
theorem ctrByte {c : Nat} (hc : c < 2 ^ 32) {k : Nat} (hk : k < 4) :
    (bswap (BitVec.ofNat 32 c)).extractLsb' (8 * k) 8 = BitVec.ofNat 8 (c / 256 ^ (3 - k)) := by
  have e : (bswap (BitVec.ofNat 32 c)).extractLsb' (8 * k) 8 = (BitVec.ofNat 32 c).extractLsb' (8 * (3 - k)) 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact bswap_bit _ hk hi
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- A byte of our part of `scratch` after a word is written there. -/
theorem sa_writeW32 (scr : BitVec 32) (m : Mem) {o i : Nat} (v : BitVec 32) (ho : o + 4 < 2 ^ 64)
    (hi : i < 2 ^ 64) :
    (m.writeW (sa scr o) v) (sa scr i) = if o ≤ i ∧ i < o + 4 then v.extractLsb' (8 * (i - o)) 8 else m (sa scr i) := by
  by_cases e : o ≤ i ∧ i < o + 4
  · rw [ite_eq_left e, show sa scr i = sa scr o + BitVec.ofNat 64 (i - o) by
      rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' e.1]]
    exact VG.X86.writeW_byte m _ v (by omega) (by decide)
  · rw [ite_eq_right e]
    refine VG.X86.writeW_byte_off m _ v _ ?_
    rw [sa, sa, Offset.sub_toNat' _ (by omega) hi]
    split <;> omega

/-! ## The parameters and the stages of an iteration -/

/-- The parameters of `mgfXor`: `DB` at `oEm + lo` (`db` bytes) and the seed
after it, fitting before `Y`; and what the caller keeps (`Inv`), with the
slots of `lo` and `db`. -/
structure MP (L : Lay) (scr : BitVec 32) (lo db : Nat) (seed : State → List Byte)
    (Inv : State → Mem → Prop) : Prop where
  hg : Geo L scr
  db0 : 0 < db
  fit : lo + db + h.D ≤ 1024
  sd : ∀ σ, (seed σ).length = h.D
  I : ∀ σ m m', Inv σ m → Frame (mgfW h L scr lo db) m m' → Inv σ m'
  lo : ∀ σ m, Inv σ m → m.readW (L.fr sLo) 32 = BitVec.ofNat 32 lo
  dbs : ∀ σ m, Inv σ m → m.readW (L.fr sDb) 32 = BitVec.ofNat 32 db

variable {lo db : Nat} {seed : State → List Byte} {Inv : State → Mem → Prop} {dbv : State → Nat → Byte}

/-- What the caller keeps, and the memory before iteration `c`. -/
abbrev MI (L : Lay) (scr : BitVec 32) (lo db c : Nat) (dbv : State → Nat → Byte) (seed : State → List Byte)
    (Inv : State → Mem → Prop) (σ : State) (m : Mem) : Prop :=
  Inv σ m ∧ MB h L scr lo db c (dbv σ) (seed σ) m

/-- What misses the slots of the counter and of the bytes masked, `DB` and the seed. -/
abbrev Away (L : Lay) (scr : BitVec 32) (lo db : Nat) (r : Region) : Prop :=
  (slotR L sCtr).Disjoint r ∧ (slotR L sDone).Disjoint r ∧ (sR scr (oEm + lo) db).Disjoint r ∧
    (sR scr (oEm + lo + db) h.D).Disjoint r

theorem MP.keep (P : MP h L scr lo db seed Inv) {c : Nat} {σ : State} {m m' : Mem} {rs : List Region}
    (hm : MI h L scr lo db c dbv seed Inv σ m) (hf : Frame rs m m') (hsub : ∀ r ∈ rs, r ∈ mgfW h L scr lo db)
    (hs : ∀ r ∈ rs, Away h L scr lo db r) : MI h L scr lo db c dbv seed Inv σ m' :=
  ⟨P.I σ m m' hm.1 (hf.mono hsub), hm.2.keep h hf (by have := P.fit; unfold oEm; omega) hs⟩

/-- What `ctHash` writes misses them. -/
theorem MP.ctW_away (P : MP h L scr lo db seed Inv) : ∀ r ∈ ctW h L scr h.B, Away h L scr lo db r := by
  have := P.fit
  have := h.B_le
  intro r hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ctW_slot h P.hg (by omega) (d := sCtr) (by decide) (by decide) (by decide) r hr
  · exact ctW_slot h P.hg (by omega) (d := sDone) (by decide) (by decide) (by decide) r hr
  · exact ctW_em h P.hg (by omega) (o := oEm + lo) (n := db) (Nat.le_add_right _ _) (by pomega) r hr
  · exact ctW_em h P.hg (by omega) (o := oEm + lo + db) (n := h.D) (by pomega) (by pomega) r hr

/-- So does a slot other than theirs. -/
theorem MP.slot_away (P : MP h L scr lo db seed Inv) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (h₁ : d + 4 ≤ sCtr ∨ sDone + 4 ≤ d) : Away h L scr lo db (slotR L d) := by
  have := P.fit
  obtain ⟨σ', ok⟩ := P.hg.ok
  have hF : d + 4 ≤ L.F + 16 := by rw [P.hg.F]; omega
  refine ⟨slotSep (by decide) hd (by unfold sCtr sDone at *; omega), slotSep (by decide) hd (by unfold sCtr sDone at *; omega),
    (P.hg.slot ok (by pomega) hF).symm, (P.hg.slot ok (by pomega) hF).symm⟩

/-- `Y`'s first block, zero. -/
abbrev Yz (scr : BitVec 32) (m : Mem) : Prop := ∀ i < h.B, m (sa scr (oY + i)) = 0

/-- `Y`'s first block: the seed, then zeros. -/
abbrev Ys (scr : BitVec 32) (sd : List Byte) (m : Mem) : Prop :=
  ∀ i < h.B, m (sa scr (oY + i)) = if i < h.D then sd.getD i 0 else 0

/-- The first block cleared. -/
theorem mgfA_vp (P : MP h L scr lo db seed Inv) (c : Nat) :
    VP (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem)
      (.seq (.block (clrArgs oY h.H.B)) zeroLoop)
      (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem ∧ Yz h scr s.mem) := by
  have hB := h.B_le
  have hB64 := h.B_ge
  have hg := P.hg
  refine VP.seq (VP.taint [.esp, .ebp] h.certs.clrY (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm⟩ => ?_)
    ((zero_vp (hg.wbuf (o := oY) (n := h.B) (by pomega) (by omega)) (by omega)
      (Inv := MI h L scr lo db c dbv seed Inv) fun σ m m' hm hf => P.keep h hm (by rwa [hg.scrA (by pomega)] at hf)
        (by simp) fun r hr => P.ctW_away h r (by simp only [List.mem_singleton] at hr; subst hr; simp)).mono
      (fun _ _ h => h) fun σ s ⟨hc, hm, hz⟩ => ⟨hc, hm, fun i hi => by
        rw [← hg.byteAt_scr (by pomega)]; exact hz i hi⟩)
  simp only [clrArgs, atS, addi, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_movi fun t3 u3 => wp_movi fun t4 u4 => WP.block_nil ?_
  refine ⟨(((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide)
    (by decide)).upd u4 (by decide) (by decide), by rw [u4.mem, u3.mem, u2.mem, u1.mem]; exact hm, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  · rw [u4.other _ (by decide), u3.gpr]
  · rw [u4.gpr]; rfl

/-- The seed to `Y`. -/
theorem mgfB_vp (P : MP h L scr lo db seed Inv) (c : Nat) :
    VP (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem ∧ Yz h scr s.mem)
      (.seq (.block (mgfSeed h.H)) Impl.Bignum.X86.copyBytes)
      (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem ∧ Ys h scr (seed σ) s.mem) := by
  have hB := h.B_le
  have hB64 := h.B_ge
  have hD := h.D_le
  have hD0 := h.D_pos
  have hN := h.N_le
  have hNL := h.NL
  have hfit := P.fit
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  -- `Y`'s bytes after the seed's place stay zero.
  let Z : State → Mem → Prop := fun σ m => MI h L scr lo db c dbv seed Inv σ m ∧
    ∀ i < h.B - h.D, m (sa scr (oY + h.D + i)) = 0
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Z σ s.mem ∧ s.gpr .ebx = scr + BitVec.ofNat 32 oY ∧
      s.gpr .esi = scr + BitVec.ofNat 32 (oEm + lo + db) ∧ s.gpr .ecx = BitVec.ofNat 32 h.D ∧
      ∀ i < h.D, s.mem (byteAt (scr + BitVec.ofNat 32 (oEm + lo + db)) i) = (seed σ).getD i 0)
    (VP.taint [.esp, .ebp] h.certs.mgfSeed (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, hz⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oY) (n := h.D) (by pomega) hD0) (hg.rbuf (o := oEm + lo + db) (n := h.D) (by pomega) hD0)
      (by rw [hg.scrA (by pomega), hg.scrA (by pomega)]; exact Geo.sep (by pomega) (by pomega) (by pomega)) hD0
      (Inv := Z) (f := fun σ i => (seed σ).getD i 0) fun σ m m' ⟨hm, hz⟩ hf => ?_).mono (fun _ _ h => h)
      fun σ s ⟨hc, ⟨hm, hz⟩, hy⟩ => ⟨hc, hm, fun i hi => ?_⟩)
  · simp only [mgfSeed, atDb, atS, addSlot, addi, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 : Ctx L scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := L.B) (by rw [c2.st.sp]) (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide))
      fun t3 u3 => ?_
    have c3 : Ctx L scr σ t3 := c2.upd u3 (by decide) (by decide)
    refine wp_addm (B := L.B) (by rw [c3.st.sp]) (by rw [hg.aFr ok sDb (by decide)]; exact c3.rFr hg sDb (by decide))
      fun t4 u4 => ?_
    refine wp_mov fun t5 u5 => wp_addi fun t6 u6 => wp_movi fun t7 u7 => WP.block_nil ?_
    have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨(((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide)
      (by decide)).upd u7 (by decide) (by decide), ⟨m7 ▸ hm, fun i hi => ?_⟩, ?_, ?_, ?_, fun i hi => ?_⟩
    · rw [m7, Nat.add_assoc]; exact hz _ (by omega)
    · simp (disch := decide) only [u7.other, u6.gpr, u5.gpr, u4.other, u3.other, u2.other, u1.other, hc.ebp]
    · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.gpr, u3.gpr, u2.gpr, u1.gpr, hc.ebp,
        u3.mem, u2.mem, u1.mem, hg.aFr ok sLo (by decide), hg.aFr ok sDb (by decide), P.lo σ _ hm.1, P.dbs σ _ hm.1,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · rw [u7.gpr]
    · rw [m7, hg.byteAt_scr (by pomega)]; exact hm.2.sd i hi
  · rw [hg.scrA (by pomega)] at hf
    refine ⟨P.keep h (rs := [sR scr oY h.B]) hm (Frame.sub hf fun r hr => ⟨sR scr oY h.B, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (Nat.le_refl _) (by omega)⟩) (by simp)
      fun r hr => P.ctW_away h r (by simp only [List.mem_singleton] at hr; subst hr; simp), ?_⟩
    exact sbytes_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)) (by pomega) hz
  · by_cases hi' : i < h.D
    · rw [ite_eq_left hi', ← hy i hi', hg.byteAt_scr (by pomega)]
    · rw [ite_eq_right hi', show oY + i = oY + h.D + (i - h.D) by omega]; exact hz _ (by omega)

/-- What `ctHash` keeps of an iteration: the memory before it, and the
slots of its message's length and blocks. -/
abbrev HI (L : Lay) (scr : BitVec 32) (lo db c : Nat) (dbv : State → Nat → Byte) (seed : State → List Byte)
    (Inv : State → Mem → Prop) (σ : State) (m : Mem) : Prop :=
  MI h L scr lo db c dbv seed Inv σ m ∧ m.readW (L.fr sL) 32 = BitVec.ofNat 32 (h.D + 4) ∧
    m.readW (L.fr sNb) 32 = BitVec.ofNat 32 1

/-- The counter after the seed in `Y`, and the slots of the message `ctHash`
hashes. -/
theorem mgfC_vp (P : MP h L scr lo db seed Inv) {c : Nat} (hc32 : c < 2 ^ 32) :
    VP (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem ∧ Ys h scr (seed σ) s.mem)
      (.block (ctrSet h.H))
      (fun σ s => Ctx L scr σ s ∧ HI h L scr lo db c dbv seed Inv σ s.mem ∧
        ∀ i < 1 * h.B, s.mem (sa scr (oY + i)) = (seed σ ++ Spec.Rsa.i2osp c 4).getD i 0) := by
  have hB := h.B_le
  have hB64 := h.B_ge
  have hD := h.D_le
  have hD0 := h.D_pos
  have hN := h.N_le
  have hone := h.one
  have hfit := P.fit
  have hg := P.hg
  have eD : h.H.D = h.D := rfl
  have eB : h.H.B = h.B := rfl
  have fit := hg.fit
  unfold oRsa at fit
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] h.certs.ctrSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, hy⟩ => ?_
  simp only [ctrSet, ld, st, mi, Impl.RsaPkcs1Sig.X86.at_]
  refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => wp_bswap fun t2 u2 => ?_
  have c2 : Ctx L scr σ t2 := c1.upd u2 (by decide) (by decide)
  have aW : VG.X86.addr scr (oY + h.H.D) = sa scr (oY + h.D) := hg.scrA (by pomega)
  refine wp_stm (B := scr) c2.ebp (by rw [aW]; exact hg.wr c2.st (by pomega)) fun t3 u3 => ?_
  have e2 : t2.gpr .eax = bswap (BitVec.ofNat 32 c) := by rw [u2.gpr, u1.gpr, hm.2.ctr]
  have m3 : t3.mem = s.mem.writeW (sa scr (oY + h.D)) (bswap (BitVec.ofNat 32 c)) := by
    rw [u3.mem, aW, e2, u2.mem, u1.mem]
  have c3 : Ctx L scr σ t3 := c2.write (rs := [sR scr oY h.B]) (by
      rw [u3.mem, aW]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) (t2.gpr .eax)
        (Offset.contains _ (by pomega) (by pomega) (by pomega)))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega))
    u3.rd u3.wr (by rw [u3.gpr]) (by rw [u3.gpr])
  refine wp_movi fun t4 u4 => (c3.upd u4 (by decide) (by decide)).wp_st hg (by decide) fun t5 c5 u5 =>
    wp_movi fun t6 u6 => (c5.upd u6 (by decide) (by decide)).wp_st hg (by decide) fun t7 c7 u7 => WP.block_nil ?_
  have m7 : t7.mem = ((s.mem.writeW (sa scr (oY + h.D)) (bswap (BitVec.ofNat 32 c))).writeW (L.fr sL)
      (BitVec.ofNat 32 (h.D + 4))).writeW (L.fr sNb) (BitVec.ofNat 32 1) := by
    rw [u7.mem, u6.mem, u6.gpr, u5.mem, u4.mem, u4.gpr, m3]
  have frS : Frame [slotR L sL, slotR L sNb] (s.mem.writeW (sa scr (oY + h.D)) (bswap (BitVec.ofNat 32 c)))
      t7.mem := by
    rw [m7]
    exact ((slot_frame L _ sL _).mono (by simp)).trans ((slot_frame L _ sNb _).mono (by simp))
  have fr : Frame [sR scr oY h.B, slotR L sL, slotR L sNb] s.mem t7.mem :=
    (((Frame.refl [sR scr oY h.B] s.mem).writeW (List.mem_singleton_self _) (bswap (BitVec.ofNat 32 c))
      (Offset.contains _ (by pomega) (by pomega) (by pomega))).mono (by simp)).trans (frS.mono (by simp))
  refine ⟨c7, ⟨P.keep h hm fr (by simp) fun r hr => ?_, ?_, ?_⟩, fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact P.ctW_away h _ (by simp)
    · exact P.slot_away h (by decide) (by decide)
    · exact P.slot_away h (by decide) (by decide)
  · rw [m7, Lay.readW_fr_other (d := sL) (e := sNb) L _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m7, Mem.readW_writeW_self32]
  rw [Nat.one_mul] at hi
  have ey : t7.mem (sa scr (oY + i)) =
      (s.mem.writeW (sa scr (oY + h.D)) (bswap (BitVec.ofNat 32 c))) (sa scr (oY + i)) :=
    sbytes_keep (o := oY) (n := h.B) (f := fun i => (s.mem.writeW (sa scr (oY + h.D))
      (bswap (BitVec.ofNat 32 c))) (sa scr (oY + i))) frS (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
      · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm) (by pomega) (fun _ _ => rfl) i hi
  rw [ey,
    sa_writeW32 scr _ _ (by pomega) (by pomega), RsaPss.getD_app, P.sd σ]
  by_cases h1 : i < h.D
  · rw [ite_eq_right (by omega), ite_eq_left h1, hy i hi, ite_eq_left h1]
  by_cases h2 : i < h.D + 4
  · rw [ite_eq_left (by omega), ite_eq_right h1, show oY + i - (oY + h.D) = i - h.D by omega,
      ctrByte hc32 (by omega), i2osp4_getD c _ (by omega)]
  · rw [ite_eq_right (by omega), ite_eq_right h1, hy i hi, ite_eq_right h1,
      getD_ge (l := Spec.Rsa.i2osp c 4) (i := i - h.D) (by rw [i2osp4_length]; omega)]

end VG.Proof.RsaPss.X86
