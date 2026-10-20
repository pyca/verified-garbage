module

import VerifiedGarbage.Proof.Cast5.X86.Round
public import VerifiedGarbage.Proof.Cast5.KeyMem
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Cast5.X86.Run
public import VerifiedGarbage.Proof.Cast5.X86.Scan

/-!
# CAST5 key expansion on 32-bit x86: a line

The memory of key expansion (`KX`): as `KMem` (`x` and `z` in the working
space, the subkeys so far), with the word below `esp` that the scans' frames
write also allowed to change.

`line l` gathers the line's four main bytes from the working space into the
lanes of `xmm0` (`gather_ok`), scans `VG_CAST5_S5678`, and XORs the four
values, the group's extra lookup and the quadruple, if any (`line_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.Lanes VG.X86.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86
open VG.Proof.Cast5 (XZ HoldsXZ Keys KMem lineOk lineVal sbox off_lt off_ge sep_base' Held tableEnt ent_table)

/-! ## The memory of key expansion -/

/-- `KMem`, with the region `B` (the word below `esp`) also allowed to change. -/
structure KX (m0 m : Mem) (c K : Addr) (B : Region) (st : XZ) (ws : List Spec.Cast5.Word) : Prop where
  xz : HoldsXZ m c st
  keys : Keys m K ws
  fr : Frame [⟨c, 64⟩, ⟨K, 128⟩, B] m0 m

theorem KX.ofKMem {m0 m m' : Mem} {c K : Addr} {B : Region} {st st' : XZ} {ws ws' : List Spec.Cast5.Word}
    (h : KX m0 m c K B st ws) (k : KMem m m' c K st' ws') : KX m0 m' c K B st' ws' :=
  ⟨k.xz, k.keys, h.fr.trans (k.fr.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl))⟩

theorem KX.kmem {m0 m : Mem} {c K : Addr} {B : Region} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KX m0 m c K B st ws) : KMem m m c K st ws := ⟨h.xz, h.keys, Frame.refl _ _⟩

/-- A write within `B`, apart from `x`, `z` and the subkeys. -/
theorem KX.inB {m0 m m' : Mem} {c K : Addr} {B : Region} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KX m0 m c K B st ws) (hf : Frame [B] m m') (dC : Region.Disjoint ⟨c, 64⟩ B)
    (dK : Region.Disjoint ⟨K, 128⟩ B) (hws : ws.length ≤ 32) : KX m0 m' c K B st ws where
  xz a i hi := by
    have := off_lt a
    rw [hf.bytes (R := ⟨c, 64⟩) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dC)
      (show (64 : Nat) ≤ 2 ^ 64 by decide) (show off a + i < 64 by omega)]
    exact h.xz a i hi
  keys i hi := by
    rw [hf.readW (r := ⟨K, 128⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dK) (by decide)]
    exact h.keys i hi
  fr := h.fr.trans (hf.mono fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; simp)

/-! ## The gather -/

/-- The index lanes of a gather: the bytes at `d`, `c`, `b`, `a`. -/
def gIdx (m : Mem) (p : Addr) (a b c d : Pos) : Nat → BitVec 32
  | 0 => (m (p + BitVec.ofNat 64 (srcOff d))).setWidth 32
  | 1 => (m (p + BitVec.ofNat 64 (srcOff c))).setWidth 32
  | 2 => (m (p + BitVec.ofNat 64 (srcOff b))).setWidth 32
  | _ => (m (p + BitVec.ofNat 64 (srcOff a))).setWidth 32

theorem srcOff_lt {q : Pos} (hq : q.2 < 16) : srcOff q + 1 ≤ 48 := by
  obtain ⟨a', i'⟩ := q; have := off_lt a'; simp only [srcOff] at hq ⊢; omega

theorem gather_ok (s : State) {S : BitVec 32} (hsi : s.gpr .esi = S) (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (S.setWidth 64) 256) {a b c d : Pos} (ha : a.2 < 16) (hb : b.2 < 16) (hc : c.2 < 16)
    (hd : d.2 < 16) :
    WP isa (.block (gather a b c d)) s fun u =>
      u.xmm .xmm0 = L (gIdx s.mem (S.setWidth 64) a b c d) ∧ u.mem = s.mem := by
  have ra := slot_rd (s := s) hfit hw (d := srcOff a) (n := 1) (by have := srcOff_lt ha; omega)
  have rb := slot_rd (s := s) hfit hw (d := srcOff b) (n := 1) (by have := srcOff_lt hb; omega)
  have rc := slot_rd (s := s) hfit hw (d := srcOff c) (n := 1) (by have := srcOff_lt hc; omega)
  have rd := slot_rd (s := s) hfit hw (d := srcOff d) (n := 1) (by have := srcOff_lt hd; omega)
  have ea := addr_off hfit (srcOff a) (by have := srcOff_lt ha; omega)
  have eb := addr_off hfit (srcOff b) (by have := srcOff_lt hb; omega)
  have ec := addr_off hfit (srcOff c) (by have := srcOff_lt hc; omega)
  have ed := addr_off hfit (srcOff d) (by have := srcOff_lt hd; omega)
  unfold gather lanes
  crun [hsi, ra, rb, rc, rd]
  rw [lanes_eq, ea, eb, ec, ed]
  rfl

/-! ## The tail of a line -/

/-- The value a line's last block computes from `v` and the memory `m`
holding its quadruple. -/
def withWord (m : Mem) (p : Addr) (v : Spec.Cast5.Word) : Option (Arr × Nat) → Spec.Cast5.Word
  | some (a, q) => v ^^^ byteRev32 (m.readW (p + BitVec.ofNat 64 (off a + 4 * q)) 32)
  | none => v

theorem tail_ok (s : State) {S : BitVec 32} (hsi : s.gpr .esi = S) (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (S.setWidth 64) 256) (l : Impl.Cast5.Line) (he : 5 ≤ l.extra.1)
    (hq : ∀ a q, l.word = some (a, q) → q < 4) {v : Nat → Spec.Cast5.Word} (h1 : s.xmm .xmm1 = L v) :
    WP isa (.block (lineTail l)) s fun u =>
      u.gpr .eax = withWord s.mem (S.setWidth 64) (v 0 ^^^ v 1 ^^^ v 2 ^^^ v 3 ^^^
        s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 (extraOff + 4 * (8 - l.extra.1))) 32) l.word ∧
      u.mem = s.mem.writeW (addr S 0) (L v) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms := by
  have e (j : Nat) (hj : j < 4) : (s.mem.writeW (addr S 0) (L v)).readW (addr S (4 * j)) 32 = v j := by
    rw [addr_off hfit (4 * j) (by omega), addr_off hfit 0 (by omega), BitVec.add_zero, rd_lane _ _ _ hj,
      dword_L _ hj]
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at e0 e1 e2 e3
  have hxo : extraOff + 4 * (8 - l.extra.1) + 4 ≤ 64 := by unfold extraOff; omega
  have ex : (s.mem.writeW (addr S 0) (L v)).readW (addr S (extraOff + 4 * (8 - l.extra.1))) 32 =
      s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 (extraOff + 4 * (8 - l.extra.1))) 32 := by
    rw [Mem.readW_writeW_sep (w := 32) (w' := 128) (slot_sep hfit (by omega) (by decide)
      (by unfold extraOff; omega) (by decide) (by decide)) (by decide), addr_off hfit _ (by omega)]
  have r0 := slot_rd hfit hw (s := s) (d := 0) (n := 4) (by decide)
  have r4 := slot_rd hfit hw (s := s) (d := 4) (n := 4) (by decide)
  have r8 := slot_rd hfit hw (s := s) (d := 8) (n := 4) (by decide)
  have r12 := slot_rd hfit hw (s := s) (d := 12) (n := 4) (by decide)
  have rx := slot_rd hfit hw (s := s) (d := extraOff + 4 * (8 - l.extra.1)) (n := 4) (by omega)
  have w0 := slot_wr hfit hw (s := s) (d := 0) (n := 16) (by decide)
  unfold lineTail
  rcases hwd : l.word with _ | ⟨a, q⟩
  · crun [hsi, h1, r0, r4, r8, r12, rx, w0, e0, e1, e2, e3, ex, List.append_nil]
    simp only [withWord]
  · have hq4 := hq a q hwd
    have hqo : off a + 4 * q + 4 ≤ 48 := by have := off_lt a; omega
    have rq := slot_rd hfit hw (s := s) (d := off a + 4 * q) (n := 4) (by omega)
    have sq : (s.mem.writeW (addr S 0) (L v)).readW (addr S (off a + 4 * q)) 32 =
        s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 (off a + 4 * q)) 32 := by
      rw [Mem.readW_writeW_sep (w := 32) (w' := 128) (slot_sep hfit (by omega) (by decide)
        (by have := off_ge a; omega) (by decide) (by decide)) (by decide), addr_off hfit _ (by omega)]
    crun [hsi, h1, r0, r4, r8, r12, rx, rq, w0, e0, e1, e2, e3, ex, sq, bswap_eq]
    simp only [withWord]

theorem ofNat_setWidth8 (x : BitVec 8) : BitVec.ofNat 8 (x.setWidth 32).toNat = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem gIdx_lt (m : Mem) (p : Addr) (a b c d : Pos) {k : Nat} (_ : k < 4) :
    (gIdx m p a b c d k).toNat < 256 := by
  have (x : Byte) : (x.setWidth 32).toNat < 256 := by
    rw [BitVec.toNat_setWidth]; have := x.isLt; omega
  match k with
  | 0 => exact this _
  | 1 => exact this _
  | 2 => exact this _
  | _ + 3 => exact this _

/-- The S-box table of key expansion. -/
abbrev tab5678 : Nat → Nat → BitVec 32 := tableEnt Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5

/-- What a line needs: the working space at `S` (`esi`), holding `x` and `z`;
the table; the word below `esp`, apart from both. -/
structure LPre (s : State) (S : BitVec 32) (st : XZ) : Prop where
  si : s.gpr .esi = S
  fitS : S.toNat + 256 ≤ 2 ^ 32
  wS : InRegions s.wr (S.setWidth 64) 256
  xz : HoldsXZ s.mem (S.setWidth 64) st
  sp : 4 ≤ (s.gpr .esp).toNat
  dS : Region.Disjoint ⟨S.setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  fitT : (s.syms Impl.Cast5.s5678Sym).toNat + 4096 ≤ 2 ^ 32
  inT : InRegions (s.rd ++ s.wr) ((s.syms Impl.Cast5.s5678Sym).setWidth 64) 4096
  dT : Region.Disjoint ⟨(s.syms Impl.Cast5.s5678Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  tab : TabAt s.mem (s.syms Impl.Cast5.s5678Sym) tab5678

/-- The registers a line writes. -/
def lineRegs : List Reg := [.eax, .ecx, .edx, .ebp]

/-- A line: `eax` := its value, with only the first 16 bytes of the working
space and the word below `esp` written. -/
theorem line_ok (s : State) {S : BitVec 32} {st : XZ} (h : LPre s S st) (l : Impl.Cast5.Line) (hl : lineOk l = true)
    (hx : s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 (extraOff + 4 * (8 - l.extra.1))) 32 =
      sbox l.extra.1 (st.get l.extra.2)) :
    WP isa (line l) s fun u => u.gpr .eax = lineVal st l ∧
      (∃ m' : Mem, ∃ w : BitVec 128, Frame [below (s.gpr .esp) 4] s.mem m' ∧ u.mem = m'.writeW (addr S 0) w) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧ Keep lineRegs s u := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he5⟩, _⟩, hwd⟩ := hl
  have gw : writesOnly lineRegs (.block (gather l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2)) = true := rfl
  have tw : writesOnly lineRegs (.block (lineTail l)) = true := by
    unfold lineTail
    rcases l.word with _ | ⟨a, q⟩ <;> rfl
  unfold line
  refine WP.seq (WP.mono_syms (WP.keep lineRegs (gather_ok s h.si h.fitS h.wS ha hb hc hd) gw)
    fun u ⟨⟨u0, um⟩, uk⟩ usy => ?_)
  have usp : u.gpr .esp = s.gpr .esp := uk.gpr .esp (by decide)
  refine WP.seq (WP.mono (scan_ok u Impl.Cast5.s5678Sym (tab := tab5678) u0
    (fun k hk => gIdx_lt _ _ _ _ _ _ hk) (by rw [usp]; exact h.sp) (by rw [usy]; exact h.fitT)
    (by rw [uk.rd, uk.wr, usy]; exact h.inT) (by rw [usy, usp]; exact h.dT) (by rw [um, usy]; exact h.tab))
    fun v ⟨v1, vk⟩ => ?_)
  have vsi : v.gpr .esi = S := (vk.gpr .esi (by decide) (by decide) (by decide)).trans
    ((uk.gpr .esi (by decide)).trans h.si)
  have hvw : InRegions v.wr (S.setWidth 64) 256 := by rw [vk.wr, uk.wr]; exact h.wS
  have hq : ∀ a q, l.word = some (a, q) → q < 4 := by
    intro a q e; rw [e] at hwd; simpa using hwd
  refine WP.mono (WP.keep lineRegs (tail_ok v vsi h.fitS hvw l he5 hq v1) tw) fun w ⟨⟨wax, wm, wrd, wwr, wsy⟩, wk⟩ => ?_
  have vf := vk.mem
  rw [um, usp] at vf
  -- The bytes the tail reads: the scan's frame wrote only below `esp`.
  have hmem (d : Nat) (hd : d + 4 ≤ 256) : v.mem.readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 =
      s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 :=
    vf.readW (r := ⟨S.setWidth 64, 256⟩) (Offset.contains_base _ hd (by omega))
      (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact h.dS) (by decide)
  have hxz : HoldsXZ v.mem (S.setWidth 64) st := fun a i hi => by
    have := off_lt a
    rw [vf.bytes (R := ⟨S.setWidth 64, 256⟩) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact h.dS)
      (show (256 : Nat) ≤ 2 ^ 64 by decide) (show off a + i < 256 by omega)]
    exact h.xz a i hi
  refine ⟨?_, ⟨v.mem, _, vf, wm⟩, wrd.trans (vk.rd.trans uk.rd), wwr.trans (vk.wr.trans uk.wr),
    wsy.trans (vk.syms.trans usy), ⟨fun r hr => ?_, wrd.trans (vk.rd.trans uk.rd), wwr.trans (vk.wr.trans uk.wr)⟩⟩
  · rw [wax, hmem _ (by unfold extraOff; omega), hx]
    simp only [tab5678, tableEnt, gIdx, ofNat_setWidth8, h.xz.pos ha, h.xz.pos hb, h.xz.pos hc, h.xz.pos hd]
    rcases hwd' : l.word with _ | ⟨a', q'⟩
    · simp only [withWord, lineVal, hwd']
    · have hq' := hq a' q' hwd'
      simp only [withWord, lineVal, hwd', ← hxz.quad a' hq', hmem _ (show off a' + 4 * q' + 4 ≤ 256 by
        have := off_lt a'; omega)]
  · have hr' := hr
    simp only [lineRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [wk.gpr r hr, vk.gpr r hr'.1 hr'.2.1 hr'.2.2.1, uk.gpr r hr]

end VG.Proof.Cast5.X86
