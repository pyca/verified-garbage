module

public import VerifiedGarbage.Proof.RsaPss.X86.CtComp
public import VerifiedGarbage.Proof.RsaPss.X86.CtSel
import VerifiedGarbage.Proof.RsaPss.X86.CtPad
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: hashing, the compression loop

`compLoop_vp`: every one of `Y`'s `nbm` blocks copied after the hash value at
`oSt` and compressed into it, and the hash value after block `lb` (the last
of the padded message, under a mask) selected into `oSel`: it is that of
`Y`'s first `lb + 1` blocks.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)

/-- `Y`'s first `T` bytes, as a list. -/
def ylist (yv : Nat → Byte) (T : Nat) : List Byte := (List.range T).map yv

theorem ylist_getD {yv : Nat → Byte} {T j : Nat} (h : j < T) : (ylist yv T).getD j 0 = yv j := by
  simp [ylist, List.getD_eq_getElem?_getD, h]

/-- `cmp d, [b + o]`, and the carry and zero flags. -/
theorem wp_cmpm {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)) →
      s'.zf = some (s.gpr d - s.mem.readW (addr B o) 32 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.mem ⟨b, o⟩) :: is)) s Q := by
  refine cons (s' := arithFlags s (s.gpr d - s.mem.readW (addr B o) 32)
    ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)
    (subOverflow (s.gpr d) (s.mem.readW (addr B o) 32) (s.gpr d - s.mem.readW (addr B o) 32)))
    (by simp [exec, execAlu, readSrc_mem hb hin]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

/-- `sub d, [b + o]`. -/
theorem wp_subm {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d - s.mem.readW (addr B o) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (by simp [exec, execAlu, readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- A hash value kept by writes elsewhere. -/
theorem stateAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (sR scr o h.N) r) : h.md.stateAt m' (sa scr o) = h.md.stateAt m (sa scr o) :=
  h.md.stateAt_congr fun _ hi => hf.bytes (R := sR scr o h.N) hd (by show h.N ≤ 2 ^ 64; have := h.N_le; omega) hi

/-- What the compression loop writes. -/
abbrev loopW (L : Lay) (scr : BitVec 32) : List Region :=
  [sR scr oSt (h.N + h.B), sR scr oCW h.H.so, sR scr oSel h.N, slotR L sBi, L.LOW]

/-- The memory of the loop's state after `b` blocks, from `Y`'s bytes `yv`
(`T` of them), with `lb` the last block of the padded message. -/
structure CM (L : Lay) (scr : BitVec 32) (T : Nat) (yv : Nat → Byte) (lb b : Nat) (m : Mem) : Prop where
  y : ∀ i < T, m (sa scr (oY + i)) = yv i
  bi : m.readW (L.fr sBi) 32 = BitVec.ofNat 32 b
  st : h.md.stateAt m (sa scr oSt) = h.md.compressList h.ok.iv (ylist yv T) b
  sel : lb < b → h.md.stateAt m (sa scr oSel) = h.md.compressList h.ok.iv (ylist yv T) (lb + 1)

/-- `CM` kept by writes that miss `Y`, `sBi` and the hash values. -/
theorem CM.keep {T : Nat} {yv : Nat → Byte} {lb b : Nat} {m m' : Mem} (hm : CM h L scr T yv lb b m)
    {rs : List Region} (fr : Frame rs m m') (hT : oY + T < 2 ^ 64)
    (dY : ∀ r ∈ rs, Region.Disjoint (sR scr oY T) r) (dB : ∀ r ∈ rs, (slotR L sBi).Disjoint r)
    (dS : ∀ r ∈ rs, Region.Disjoint (sR scr oSt h.N) r) (dE : ∀ r ∈ rs, Region.Disjoint (sR scr oSel h.N) r) :
    CM h L scr T yv lb b m' :=
  ⟨sbytes_keep fr dY hT hm.y, slot_keep fr dB hm.bi, by rw [stateAt_keep h fr dS, hm.st],
    fun hl => by rw [stateAt_keep h fr dE, hm.sel hl]⟩

/-- The compression loop. -/
theorem compLoop_vp (hg : Geo L scr) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {yv : State → Nat → Byte} {lb : State → Nat} (hlb : ∀ σ, lb σ < nbm)
    {Inv : State → Mem → Prop} (hI : ∀ σ m m', Inv σ m → Frame (loopW h L scr) m m' → Inv σ m')
    (hslb : ∀ σ m, Inv σ m → m.readW (L.fr sLb) 32 = BitVec.ofNat 32 (lb σ))
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ (∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = yv σ i) ∧
        h.md.stateAt s.mem (sa scr oSt) = h.ok.iv)
      (compLoop h.H)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ h.md.stateAt s.mem (sa scr oSel) =
        h.md.compressList h.ok.iv (ylist (yv σ) (nbm * h.B)) (lb σ + 1)) := by
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
  have hC : L.C ≤ 2 ^ 32 := by have := ok.BC; have := L.B.isLt; omega
  have nbB : nbm ≤ nbm * h.B := Nat.le_mul_of_pos_right nbm (by omega)
  generalize hT : nbm * h.B = T at hnb nbB ⊢
  -- What the pieces write, against what they keep.
  have sl : ∀ d, d + 4 ≤ frameBytes → ∀ {o n : Nat}, o + n ≤ oRsa → (slotR L d).Disjoint (sR scr o n) :=
    fun d hd o n h => hg.slot ok h (by rw [hg.F]; omega)
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
  refine VP.seq (G := CS 0) (VP.taint [.esp, .ebp] compInit_taint (sp_bp fun _ _ h => h.1)
    fun σ s ⟨hc, hi, hy, hst⟩ => ?_) ?_
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
  refine (VP.loop (I := fun n σ s => n ≤ nbm ∧ CS (nbm - n) σ s) (fun n => ?_) (nbm - 1)).mono
    (fun σ s hs => ⟨by omega, by rw [show nbm - (nbm - 1 + 1) = 0 by omega]; exact hs⟩) fun _ _ h => h
  by_cases hn : n + 1 ≤ nbm
  swap
  · exact VP.empty fun σ s ⟨h, _⟩ => hn h
  generalize hb : nbm - (n + 1) = b
  have hbn : b < nbm := by omega
  have hbB : b * h.B + h.B ≤ T := by rw [← hT, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
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
    (.seq h.H.cmp (.seq (.block (selSet h.H)) (.seq (countLoop selBody) (.block compNext))))))) _
  refine VP.seq (G := fun σ s => CS b σ s ∧ s.gpr .esi = scr + BitVec.ofNat 32 (oY + b * h.B) ∧
      s.gpr .ebx = scr + BitVec.ofNat 32 (oSt + h.N) ∧ s.gpr .ecx = BitVec.ofNat 32 h.B) ?_
    (VP.seq (G := fun σ s => Ctx L scr σ s ∧ X1 σ s.mem ∧
        ∀ i < h.B, s.mem (sa scr (oSt + h.N + i)) = yv σ (b * h.B + i)) ?_
    (VP.seq (G := fun σ s => (Ctx L scr σ s ∧ X1 σ s.mem ∧
        ∀ i < h.B, s.mem (sa scr (oSt + h.N + i)) = yv σ (b * h.B + i)) ∧
        s.gpr .ebx = scr + BitVec.ofNat 32 oSt ∧ s.gpr .eax = scr + BitVec.ofNat 32 (oSt + h.N)) ?_
    (VP.seq (G := fun σ s => Ctx L scr σ s ∧ X3 σ s.mem) ?_
    (VP.seq (G := fun σ s => (Ctx L scr σ s ∧ X3 σ s.mem) ∧ s.gpr .esi = scr + BitVec.ofNat 32 oSt ∧
        s.gpr .edi = scr + BitVec.ofNat 32 oSel ∧ s.gpr .ecx = BitVec.ofNat 32 h.N ∧
        s.gpr .edx = maskOf (b = lb σ)) ?_
    (VP.seq (G := fun σ s => Ctx L scr σ s ∧ X4 σ s.mem) ?_ ?_)))))
  · -- The block's address, and where it goes.
    refine VP.taint [.esp, .ebp] h.certs.blkSet (sp_bp fun _ _ h => h.2.1) fun σ s ⟨hn', hc, hi, hm⟩ => ?_
    simp only [blkSet, atS, ld, mi, addi, List.cons_append, List.nil_append, List.append_assoc]
    refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
    refine wp_shl (lgB h.H) (n := b) (by rw [h.pow_lg]; omega) (by rw [u1.gpr, hm.bi]) fun t2 u2 => ?_
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
    refine (copy_vp (hg.wbuf (o := oSt + h.N) (n := h.B) (by omega_arith) (by omega))
      (hg.rbuf (o := oY + b * h.B) (n := h.B) (by omega_arith) (by omega))
      (by rw [aS, aD]; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)) (by omega) (Inv := X1)
      (f := fun σ i => yv σ (b * h.B + i)) ?_).mono
      (fun σ s ⟨⟨hc, hi, hm⟩, si, bx, cx⟩ => ⟨hc, ⟨hi, hm⟩, bx, si, cx, fun i hi' => ?_⟩)
      fun σ s ⟨hc, hx, hb'⟩ => ⟨hc, hx, fun i hi' => ?_⟩
    · intro σ m m' ⟨hi, hm⟩ fr
      rw [aD] at fr
      have one : ∀ {P : Region → Prop}, P (sR scr (oSt + h.N) h.B) → ∀ r ∈ [sR scr (oSt + h.N) h.B], P r := by
        intro P hP r hr; simp only [List.mem_singleton] at hr; subst hr; exact hP
      exact ⟨hI σ _ _ hi (fr.sub (one ⟨sR scr oSt (h.N + h.B), by simp [loopW], Offset.sub _ (by omega) (by omega)⟩)),
        hm.keep h fr (by omega_arith) (one (Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)))
          (one (sl sBi (by decide) (by omega_arith))) (one (Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)))
          (one (Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)))⟩
    · rw [hg.byteAt_scr (by omega_arith), Nat.add_assoc]; exact hm.y _ (by omega)
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
    refine (comp_vp h hg (X := fun σ m => X1 σ m ∧
        ∀ i < h.B, m (sa scr (oSt + h.N + i)) = yv σ (b * h.B + i))).mono
      (fun σ s ⟨⟨hc, hx, hblk⟩, bx, ax⟩ => ⟨hc, ⟨hx, hblk⟩, bx, ax⟩)
      fun σ s ⟨hc, m₀, ⟨⟨hi, hm⟩, hblk⟩, fr, e⟩ => ⟨hc, hI σ _ _ hi (fr.sub fun r hr => ?_), ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sR scr oSt (h.N + h.B), by simp [loopW], Offset.sub _ (by omega) (by omega)⟩
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
        ylist_getD (by have := Nat.mul_comm b h.B; omega), Nat.mul_comm]
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
    · have hb32 : b < 2 ^ 32 := by omega
      have hl32 : lb σ < 2 ^ 32 := by have := hlb σ; omega
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
      · have hl' : lb σ < b := by omega
        rw [← hsel hl']
        refine h.md.stateAt_congr fun i hi' => ?_
        rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa, hb' i hi', ite_eq_right e]
  · -- The next block.
    refine VP.taint [.esp, .ebp] compNext_taint (sp_bp fun _ _ h => h.1)
      fun σ s ⟨hc, hi, hy, hbi, hst, hsel⟩ => ?_
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
      sub_beq (a := b + 1) (b := nbm) (by omega) (by omega)] at z
    refine ⟨?_, fun h0 => ⟨hc', hi', hsel' (by have := hlb σ; omega)⟩, fun hp => ⟨by omega, ?_⟩⟩
    · show eval .ne t4 = _
      simp only [eval, z]
      by_cases h0 : n = 0
      · simp [h0]; omega
      · have h1 : 0 < n := Nat.pos_of_ne_zero h0
        simp [h1]; omega
    rw [show nbm - n = b + 1 by omega]
    refine ⟨hc', hi', ⟨sbytes_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (sl sBi (by decide) (by omega_arith)).symm) (by omega_arith) hy,
      by rw [m4, Mem.readW_writeW_self32], ?_, hsel'⟩⟩
    rw [stateAt_keep h fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (sl sBi (by decide) (by omega_arith)).symm), hst]

end VG.Proof.RsaPss.X86
