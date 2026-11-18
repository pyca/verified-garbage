module

public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.TaintSym
public import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.TaintSym
meta import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Cast5.X86.Round
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Cast5.X86.Ecb
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Cast5.KeyMem
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Cast5.X86.Run
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Cast5.X86.Round
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.Cast5.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Cast5.KeyMem
meta import VerifiedGarbage.Proof.Cast5.Table
meta import VerifiedGarbage.Proof.Cast5.X86.Run
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Framework.X86.SseDword

/-! ### `Cast5.X86.Key`, which only this module used -/

section

/-! ### `Cast5.X86.KeyGroup`, which this module and modules that import it used -/

section

/-! ### `Cast5.X86.KeyLine`, which only this module used -/

section

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
      (show (64 : Nat) ≤ 2 ^ 64 by decide) (show off a + i < 64 by omega_using [hi, this])]
    exact h.xz a i hi
  keys i hi := by
    rw [hf.readW (r := ⟨K, 128⟩) (Offset.contains_base _ (by omega_using [hws, hi]) (by omega_using [hws, hi]))
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
  obtain ⟨a', i'⟩ := q; have := off_lt a'; simp only [srcOff] at hq ⊢; omega_using [hq, this]

theorem gather_ok (s : State) {S : BitVec 32} (hsi : s.gpr .esi = S) (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (S.setWidth 64) 256) {a b c d : Pos} (ha : a.2 < 16) (hb : b.2 < 16) (hc : c.2 < 16)
    (hd : d.2 < 16) :
    WP isa (.block (gather a b c d)) s fun u =>
      u.xmm .xmm0 = L (gIdx s.mem (S.setWidth 64) a b c d) ∧ u.mem = s.mem := by
  have ra := slot_rd (s := s) hfit hw (d := srcOff a) (n := 1) (by have := srcOff_lt ha; omega_using [this])
  have rb := slot_rd (s := s) hfit hw (d := srcOff b) (n := 1) (by have := srcOff_lt hb; omega_using [this])
  have rc := slot_rd (s := s) hfit hw (d := srcOff c) (n := 1) (by have := srcOff_lt hc; omega_using [this])
  have rd := slot_rd (s := s) hfit hw (d := srcOff d) (n := 1) (by have := srcOff_lt hd; omega_using [this])
  have ea := addr_off hfit (srcOff a) (by have := srcOff_lt ha; omega_using [this])
  have eb := addr_off hfit (srcOff b) (by have := srcOff_lt hb; omega_using [this])
  have ec := addr_off hfit (srcOff c) (by have := srcOff_lt hc; omega_using [this])
  have ed := addr_off hfit (srcOff d) (by have := srcOff_lt hd; omega_using [this])
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
    rw [addr_off hfit (4 * j) (by omega_using [hj]), addr_off hfit 0 (by omega_using []), BitVec.add_zero, rd_lane _ _ _ hj,
      dword_L _ hj]
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at e0 e1 e2 e3
  have hxo : extraOff + 4 * (8 - l.extra.1) + 4 ≤ 64 := by unfold extraOff; omega_using [he]
  have ex : (s.mem.writeW (addr S 0) (L v)).readW (addr S (extraOff + 4 * (8 - l.extra.1))) 32 =
      s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 (extraOff + 4 * (8 - l.extra.1))) 32 := by
    rw [Mem.readW_writeW_sep (w := 32) (w' := 128) (slot_sep hfit (by omega_using [hxo]) (by decide)
      (by unfold extraOff; omega_using []) (by decide) (by decide)) (by decide), addr_off hfit _ (by omega_using [hxo])]
  have r0 := slot_rd hfit hw (s := s) (d := 0) (n := 4) (by decide)
  have r4 := slot_rd hfit hw (s := s) (d := 4) (n := 4) (by decide)
  have r8 := slot_rd hfit hw (s := s) (d := 8) (n := 4) (by decide)
  have r12 := slot_rd hfit hw (s := s) (d := 12) (n := 4) (by decide)
  have rx := slot_rd hfit hw (s := s) (d := extraOff + 4 * (8 - l.extra.1)) (n := 4) (by omega_using [hxo])
  have w0 := slot_wr hfit hw (s := s) (d := 0) (n := 16) (by decide)
  unfold lineTail
  rcases hwd : l.word with _ | ⟨a, q⟩
  · crun [hsi, h1, r0, r4, r8, r12, rx, w0, e0, e1, e2, e3, ex, List.append_nil]
    simp only [withWord]
  · have hq4 := hq a q hwd
    have hqo : off a + 4 * q + 4 ≤ 48 := by have := off_lt a; omega_using [hq4, this]
    have rq := slot_rd hfit hw (s := s) (d := off a + 4 * q) (n := 4) (by omega_using [hqo])
    have sq : (s.mem.writeW (addr S 0) (L v)).readW (addr S (off a + 4 * q)) 32 =
        s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 (off a + 4 * q)) 32 := by
      rw [Mem.readW_writeW_sep (w := 32) (w' := 128) (slot_sep hfit (by omega_using [hqo]) (by decide)
        (by have := off_ge a; omega_using [this]) (by decide) (by decide)) (by decide), addr_off hfit _ (by omega_using [hqo])]
    crun [hsi, h1, r0, r4, r8, r12, rx, rq, w0, e0, e1, e2, e3, ex, sq, bswap_eq]
    simp only [withWord]

theorem ofNat_setWidth8 (x : BitVec 8) : BitVec.ofNat 8 (x.setWidth 32).toNat = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have := x.isLt
  omega_using []

theorem gIdx_lt (m : Mem) (p : Addr) (a b c d : Pos) {k : Nat} (_ : k < 4) :
    (gIdx m p a b c d k).toNat < 256 := by
  have (x : Byte) : (x.setWidth 32).toNat < 256 := by
    rw [BitVec.toNat_setWidth]; have := x.isLt; omega_using []
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
    vf.readW (r := ⟨S.setWidth 64, 256⟩) (Offset.contains_base _ hd (by omega_using [hd]))
      (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact h.dS) (by decide)
  have hxz : HoldsXZ v.mem (S.setWidth 64) st := fun a i hi => by
    have := off_lt a
    rw [vf.bytes (R := ⟨S.setWidth 64, 256⟩) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact h.dS)
      (show (256 : Nat) ≤ 2 ^ 64 by decide) (show off a + i < 256 by omega_using [hi, this])]
    exact h.xz a i hi
  refine ⟨?_, ⟨v.mem, _, vf, wm⟩, wrd.trans (vk.rd.trans uk.rd), wwr.trans (vk.wr.trans uk.wr),
    wsy.trans (vk.syms.trans usy), ⟨fun r hr => ?_, wrd.trans (vk.rd.trans uk.rd), wwr.trans (vk.wr.trans uk.wr)⟩⟩
  · rw [wax, hmem _ (by unfold extraOff; omega_using []), hx]
    simp only [tab5678, tableEnt, gIdx, ofNat_setWidth8, h.xz.pos ha, h.xz.pos hb, h.xz.pos hc, h.xz.pos hd]
    rcases hwd' : l.word with _ | ⟨a', q'⟩
    · simp only [withWord, lineVal, hwd']
    · have hq' := hq a' q' hwd'
      simp only [withWord, lineVal, hwd', ← hxz.quad a' hq', hmem _ (show off a' + 4 * q' + 4 ≤ 256 by
        have := off_lt a'; omega_using [hq', this])]
  · have hr' := hr
    simp only [lineRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [wk.gpr r hr, vk.gpr r hr'.1 hr'.2.1 hr'.2.2.1, uk.gpr r hr]

end VG.Proof.Cast5.X86

end

end


/-!
# CAST5 key expansion on 32-bit x86: groups of four lines

A group (`lines4`) makes its four extra lookups (`extras_ok`), then runs its
lines, each storing its value into `x` or `z` (`groupQ_ok`) or as the next
subkey (`groupK_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.Lanes VG.X86.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86
open VG.Proof.Cast5 (XZ HoldsXZ Keys KMem lineOk lineVal sbox off_lt off_ge sep_base' Held tableEnt ent_table
  exVal exVal_sbox runQ runQ_succ get_runQ GroupOk keys4 take_keys4)

/-- The group's extra lookups, lanes `0 … 3` at `c + 48`. -/
def Extras (m : Mem) (c : Addr) (f : Nat → Spec.Cast5.Word) : Prop :=
  ∀ j < 4, m.readW (c + BitVec.ofNat 64 (extraOff + 4 * j)) 32 = f j

/-- `Extras` after a write of `w / 8` bytes at `c + d`, below them. -/
theorem Extras.write {m : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {d w : Nat}
    (v : BitVec w) (hd : d + w / 8 ≤ extraOff) :
    Extras (m.writeW (c + BitVec.ofNat 64 d) v) c f := fun j hj => by
  rw [Mem.readW_writeW_sep (Offset.sep c (by unfold extraOff at *; omega_arith) (by unfold extraOff; omega_arith)
    (by unfold extraOff at *; omega_arith)) (by decide)]
  exact h j hj

/-- `Extras` after a write elsewhere. -/
theorem Extras.write_disj {m : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {a : Addr}
    {w : Nat} (v : BitVec w) (hd : Region.Disjoint ⟨c, 64⟩ ⟨a, w / 8⟩) :
    Extras (m.writeW a v) c f := fun j hj => by
  rw [Mem.readW_writeW_sep (hd.sep (Offset.contains_base c (by unfold extraOff; omega_arith)
    (by unfold extraOff; omega_arith)) (Region.contains_self _ _)) (by decide)]
  exact h j hj

/-- `Extras` after a frame apart from them. -/
theorem Extras.frame {m m' : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {B : Region}
    (hf : Frame [B] m m') (hd : Region.Disjoint ⟨c, 64⟩ B) : Extras m' c f := fun j hj => by
  rw [hf.readW (r := ⟨c, 64⟩) (Offset.contains_base c (by unfold extraOff; omega_arith) (by unfold extraOff; omega_arith))
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd) (by decide)]
  exact h j hj

/-- The state of key expansion from the memory `m0`: the working space at
`S` (`esi`), writable, as is the schedule `K`; the table; the word below `esp`
(`B`), which the scans' frames write; and the memory (`KX`). -/
structure KS (m0 : Mem) (S : BitVec 32) (K : Addr) (s : State) (st : XZ) (ws : List Spec.Cast5.Word) : Prop where
  si : s.gpr .esi = S
  fitS : S.toNat + 256 ≤ 2 ^ 32
  wS : InRegions s.wr (S.setWidth 64) 256
  mem : KX m0 s.mem (S.setWidth 64) K (below (s.gpr .esp) 4) st ws
  len : ws.length ≤ 32
  wK : InRegions s.wr K 128
  dKS : Region.Disjoint ⟨K, 128⟩ ⟨S.setWidth 64, 256⟩
  sp : 4 ≤ (s.gpr .esp).toNat
  dS : Region.Disjoint ⟨S.setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  dK : Region.Disjoint ⟨K, 128⟩ (below (s.gpr .esp) 4)
  fitT : (s.syms s5678Sym).toNat + 4096 ≤ 2 ^ 32
  inT : InRegions (s.rd ++ s.wr) ((s.syms s5678Sym).setWidth 64) 4096
  dT : ∀ r ∈ ([⟨S.setWidth 64, 256⟩, ⟨K, 128⟩, below (s.gpr .esp) 4] : List Region),
    Region.Disjoint ⟨(s.syms s5678Sym).setWidth 64, 4096⟩ r
  held : Held m0 ((s.syms s5678Sym).setWidth 64) Impl.Cast5.s5678

theorem addr_zero {S : BitVec 32} (h : S.toNat + 256 ≤ 2 ^ 32) : addr S 0 = S.setWidth 64 := by
  rw [addr_off h 0 (by decide)]; exact BitVec.add_zero _

theorem s5678_length : Impl.Cast5.s5678.length = 512 := Proof.Cast5.table_length _ _ _ _

theorem sub64 (c : Addr) : Region.Sub ⟨c, 64⟩ ⟨c, 256⟩ := Region.sub_prefix (by decide)

theorem KS.dKS64 {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) : Region.Disjoint ⟨K, 128⟩ ⟨S.setWidth 64, 64⟩ := h.dKS.sub_right (sub64 _)

/-- The table's entries, now. -/
theorem KS.tab {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) : TabAt s.mem (s.syms s5678Sym) tab5678 := by
  have hheld : Held s.mem ((s.syms s5678Sym).setWidth 64) Impl.Cast5.s5678 := fun i hi => by
    rw [s5678_length] at hi
    rw [h.mem.fr.readW (r := ⟨(s.syms s5678Sym).setWidth 64, 4096⟩)
      (Offset.contains_base _ (by omega_arith) (by have := h.fitT; omega_arith)) (fun r hr => ?_) (by decide)]
    · exact h.held i (by rw [s5678_length]; exact hi)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (h.dT ⟨S.setWidth 64, 256⟩ (by simp)).sub_right (sub64 _)
      · exact h.dT ⟨K, 128⟩ (by simp)
      · exact h.dT (below (s.gpr .esp) 4) (by simp)
  exact fun j hj k hk => Proof.Cast5.ent_table hheld hj hk

/-- What a line needs, from a state of key expansion. -/
theorem KS.lpre {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) : LPre s S st :=
  ⟨h.si, h.fitS, h.wS, h.mem.xz, h.sp, h.dS, h.fitT, h.inT, h.dT _ (by simp), h.tab⟩

/-- The same state, later: other registers but `esi` and `esp`, memory and flags. -/
theorem KS.update {m0 : Mem} {S : BitVec 32} {K : Addr} {s u : State} {st st' : XZ}
    {ws ws' : List Spec.Cast5.Word} (h : KS m0 S K s st ws) (hsi : u.gpr .esi = s.gpr .esi)
    (hsp : u.gpr .esp = s.gpr .esp) (hm : KX m0 u.mem (S.setWidth 64) K (below (s.gpr .esp) 4) st' ws')
    (hl : ws'.length ≤ 32) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) (hsy : u.syms = s.syms) :
    KS m0 S K u st' ws' where
  si := hsi.trans h.si
  fitS := h.fitS
  wS := by rw [hwr]; exact h.wS
  mem := by rw [hsp]; exact hm
  len := hl
  wK := by rw [hwr]; exact h.wK
  dKS := h.dKS
  sp := by rw [hsp]; exact h.sp
  dS := by rw [hsp]; exact h.dS
  dK := by rw [hsp]; exact h.dK
  fitT := by rw [hsy]; exact h.fitT
  inT := by rw [hsy, hrd, hwr]; exact h.inT
  dT := by rw [hsy, hsp]; exact h.dT
  held := by rw [hsy]; exact h.held

/-- A line's memory, as a state of key expansion. -/
theorem KS.afterLine {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) {m' : Mem} {w : BitVec 128} (hf : Frame [below (s.gpr .esp) 4] s.mem m') :
    KX m0 (m'.writeW (S.setWidth 64) w) (S.setWidth 64) K (below (s.gpr .esp) 4) st ws := by
  have k1 := h.mem.inB hf (h.dS.sub_left (sub64 _)) h.dK h.len
  have k2 := KMem.write k1.kmem h.dKS64 h.len (d := 0) w (by decide) (.inl (by decide))
  rw [BitVec.add_zero] at k2
  exact k1.ofKMem k2

/-- A store of `xmm1` to the working space. -/
theorem store16_ok (v : State) {S : BitVec 32} (hsi : v.gpr .esi = S) (d : Nat)
    (h : InRegions v.wr (addr S d) 16) :
    WP isa (.block [.movdquStore (at_ .esi d) .xmm1]) v fun w =>
      w.mem = v.mem.writeW (addr S d) (v.xmm .xmm1) ∧ w.gpr = v.gpr ∧
        w.rd = v.rd ∧ w.wr = v.wr ∧ w.syms = v.syms := by
  crun [hsi, h]

theorem extras_ok {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) {a b c' d : Pos} (ha : a.2 < 16) (hb : b.2 < 16) (hc : c'.2 < 16) (hd : d.2 < 16) :
    WP isa (extras a b c' d) s fun u => KS m0 S K u st ws ∧ Extras u.mem (S.setWidth 64) (exVal st a b c' d) ∧
      u.syms = s.syms ∧ Keep lineRegs s u := by
  have gw : writesOnly lineRegs (.block (gather a b c' d)) = true := rfl
  unfold extras
  refine WP.seq (WP.mono_syms (WP.keep lineRegs (gather_ok s h.si h.fitS h.wS ha hb hc hd) gw)
    fun u ⟨⟨u0, um⟩, uk⟩ usy => ?_)
  have usp : u.gpr .esp = s.gpr .esp := uk.gpr .esp (by decide)
  refine WP.seq (WP.mono (scan_ok u s5678Sym (tab := tab5678) u0
    (fun k hk => gIdx_lt _ _ _ _ _ _ hk) (by rw [usp]; exact h.sp) (by rw [usy]; exact h.fitT)
    (by rw [uk.rd, uk.wr, usy]; exact h.inT) (by rw [usy, usp]; exact h.dT _ (by simp))
    (by rw [um, usy]; exact h.tab)) fun v ⟨v1, vk⟩ => ?_)
  have vsi : v.gpr .esi = S := (vk.gpr .esi (by decide) (by decide) (by decide)).trans
    ((uk.gpr .esi (by decide)).trans h.si)
  have h48 : InRegions v.wr (addr S extraOff) 16 := by
    rw [vk.wr, uk.wr]; exact slot_wr h.fitS h.wS (by decide)
  refine WP.mono (store16_ok v vsi extraOff h48) fun w ⟨wm, wg, wrd, wwr, wsy⟩ => ?_
  have vf := vk.mem
  rw [um, usp] at vf
  rw [v1] at wm
  have k1 := h.mem.inB vf (h.dS.sub_left (sub64 _)) h.dK h.len
  have k2 := KMem.write k1.kmem h.dKS64 h.len (d := extraOff) (L fun k => tab5678
    (gIdx s.mem (S.setWidth 64) a b c' d k).toNat k) (by decide) (.inr (by decide))
  rw [← addr_off h.fitS extraOff (by decide), ← wm] at k2
  have wsp : w.gpr .esp = s.gpr .esp := by rw [wg, vk.gpr .esp (by decide) (by decide) (by decide), usp]
  refine ⟨h.update (by rw [wg, vsi, h.si]) wsp (k1.ofKMem k2) h.len (by rw [wrd, vk.rd, uk.rd])
    (by rw [wwr, vk.wr, uk.wr]) (by rw [wsy, vk.syms, usy]), fun j hj => ?_, by rw [wsy, vk.syms, usy],
    ⟨fun r hr => ?_, by rw [wrd, vk.rd, uk.rd], by rw [wwr, vk.wr, uk.wr]⟩⟩
  · rw [wm, addr_off h.fitS extraOff (by decide), ← Proof.Cast5.add_ofNat_add, rd_lane _ _ _ hj, dword_L _ hj]
    rcases cases4 hj with rfl | rfl | rfl | rfl <;>
      simp only [tab5678, tableEnt, gIdx, exVal, ofNat_setWidth8, h.mem.xz.pos ha, h.mem.xz.pos hb,
        h.mem.xz.pos hc, h.mem.xz.pos hd]
  · have hr' := hr
    simp only [lineRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [wg, vk.gpr r hr'.1 hr'.2.1 hr'.2.2.1, uk.gpr r hr]

theorem storeQuad_ok (u : State) {S : BitVec 32} (hsi : u.gpr .esi = S) (a : Arr) (q : Nat) {v : Spec.Cast5.Word}
    (hax : u.gpr .eax = v) (hw : InRegions u.wr (addr S (off a + 4 * q)) 4) :
    WP isa (.block (storeQuad a q)) u fun w =>
      w.mem = u.mem.writeW (addr S (off a + 4 * q)) (byteRev32 v) ∧
      (∀ r, r ≠ .eax → w.gpr r = u.gpr r) ∧ w.rd = u.rd ∧ w.wr = u.wr ∧ w.syms = u.syms := by
  unfold storeQuad
  crun [hsi, hax, hw, bswap_eq]
  exact fun r hr => ite_eq_right hr

theorem storeKey_ok (u : State) {E : BitVec 32} (hdi : u.gpr .edi = E) (k : Nat) {v : Spec.Cast5.Word}
    (hax : u.gpr .eax = v) (hw : InRegions u.wr (addr E (4 * k)) 4) :
    WP isa (.block (storeKey k)) u fun w =>
      w.mem = u.mem.writeW (addr E (4 * k)) v ∧ w.gpr = u.gpr ∧ w.rd = u.rd ∧ w.wr = u.wr ∧ w.syms = u.syms := by
  unfold storeKey
  crun [hdi, hax, hw]

theorem lineOk_extra {l : Impl.Cast5.Line} (hl : lineOk l = true) : 5 ≤ l.extra.1 ∧ l.extra.1 ≤ 8 := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  exact ⟨hl.1.1.2, hl.1.2⟩

/-- The line, from a state of key expansion. -/
theorem lineS_ok {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) {f : Nat → Spec.Cast5.Word} (hE : Extras s.mem (S.setWidth 64) f)
    {l : Impl.Cast5.Line} (hl : lineOk l = true) (hx : f (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2)) :
    WP isa (line l) s fun u => u.gpr .eax = lineVal st l ∧ KS m0 S K u st ws ∧
      Extras u.mem (S.setWidth 64) f ∧ u.syms = s.syms ∧ Keep lineRegs s u := by
  have he := lineOk_extra hl
  have hx' : s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 (extraOff + 4 * (8 - l.extra.1))) 32 =
      sbox l.extra.1 (st.get l.extra.2) := by rw [hE _ (by omega_arith), hx]
  refine WP.mono (line_ok s h.lpre l hl hx') fun u ⟨uax, ⟨m', w, hf, um⟩, urd, uwr, usy, uk⟩ => ?_
  have usp : u.gpr .esp = s.gpr .esp := uk.gpr .esp (by decide)
  have hE0 := (hE.frame hf (h.dS.sub_left (sub64 _))).write (d := 0) w (by decide)
  rw [BitVec.add_zero] at hE0
  rw [addr_zero h.fitS] at um
  rw [← um] at hE0
  exact ⟨uax, h.update (uk.gpr .esi (by decide)) usp (by rw [um]; exact h.afterLine hf) h.len urd uwr usy, hE0,
    usy, uk⟩

/-- A line storing into quadruple `q` of `a`. -/
theorem lineQ_ok {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) {f : Nat → Spec.Cast5.Word} (hE : Extras s.mem (S.setWidth 64) f)
    {l : Impl.Cast5.Line} (hl : lineOk l = true) (hx : f (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2))
    (a : Arr) {q : Nat} (hq : q < 4) :
    WP isa (line l) s fun u => WP isa (.block (storeQuad a q)) u fun v =>
      KS m0 S K v (st.put a q (lineVal st l)) ws ∧ Extras v.mem (S.setWidth 64) f ∧ v.syms = s.syms ∧
        Keep lineRegs s v := by
  refine WP.mono (lineS_ok h hE hl hx) fun u ⟨uax, hu, uE, usy, uk⟩ => ?_
  have := off_lt a
  have hw : InRegions u.wr (addr S (off a + 4 * q)) 4 := slot_wr hu.fitS hu.wS (by omega_arith)
  refine WP.mono (storeQuad_ok u hu.si a q uax hw) fun v ⟨vm, vg, vrd, vwr, vsy⟩ => ?_
  have k := KMem.quad hu.mem.kmem hu.dKS64 hu.len a hq (lineVal st l)
  rw [← addr_off hu.fitS _ (by omega_arith), ← vm] at k
  refine ⟨hu.update (vg _ (by decide)) (vg _ (by decide)) (hu.mem.ofKMem k) hu.len vrd vwr vsy,
    by rw [vm, addr_off hu.fitS _ (by omega_arith)]; exact uE.write _ (by unfold extraOff; omega_arith), by rw [vsy, usy],
    ⟨fun r hr => by rw [vg r (fun e => hr (e ▸ List.mem_cons_self)), uk.gpr r hr], by rw [vrd, uk.rd],
      by rw [vwr, uk.wr]⟩⟩

/-- A line storing the next subkey, `k` of those from `edi`. -/
theorem lineK_ok {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) {f : Nat → Spec.Cast5.Word} (hE : Extras s.mem (S.setWidth 64) f)
    {l : Impl.Cast5.Line} (hl : lineOk l = true) (hx : f (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2))
    {k : Nat} {E : BitVec 32} (hdi : s.gpr .edi = E)
    (hadr : addr E (4 * k) = K + BitVec.ofNat 64 (4 * ws.length)) (hlen : ws.length < 32) :
    WP isa (line l) s fun u => WP isa (.block (storeKey k)) u fun v =>
      KS m0 S K v st (ws ++ [lineVal st l]) ∧ Extras v.mem (S.setWidth 64) f ∧ v.syms = s.syms ∧
        Keep lineRegs s v := by
  refine WP.mono (lineS_ok h hE hl hx) fun u ⟨uax, hu, uE, usy, uk⟩ => ?_
  have hw : InRegions u.wr (addr E (4 * k)) 4 := by
    rw [hadr]; exact CallLay.inRegions_sub hu.wK (by omega_arith) (by decide)
  refine WP.mono (storeKey_ok u (by rw [uk.gpr .edi (by decide), hdi]) k uax hw)
    fun v ⟨vm, vg, vrd, vwr, vsy⟩ => ?_
  rw [hadr] at vm
  have hd : Region.Disjoint ⟨S.setWidth 64, 64⟩ ⟨K + BitVec.ofNat 64 (4 * ws.length), 32 / 8⟩ :=
    (hu.dKS64.sub_left (Offset.sub_base K (by omega_arith))).symm
  have km := KMem.key hu.mem.kmem hu.dKS64 hlen (lineVal st l)
  rw [← vm] at km
  refine ⟨hu.update (by rw [vg]) (by rw [vg]) (hu.mem.ofKMem km)
      (by rw [List.length_append, List.length_singleton]; omega_arith) vrd vwr vsy,
    by rw [vm]; exact uE.write_disj _ hd, by rw [vsy, usy],
    ⟨fun r hr => by rw [vg, uk.gpr r hr], by rw [vrd, uk.rd], by rw [vwr, uk.wr]⟩⟩

/-- A group of lines: its extra lookups, then each line and its store. -/
theorem lines4_ok {ls : List Impl.Cast5.Line} {stk : Nat → List Instr} {s : State} (I : Nat → State → Prop)
    (h0 : WP isa (extras (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) s (I 0))
    (hk : ∀ k < 4, ∀ u, I k u →
      WP isa (line (ls.getD k default)) u fun v => WP isa (.block (stk k)) v (I (k + 1))) :
    WP isa (lines4 ls stk) s (I 4) := by
  unfold lines4
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.foldr_cons, List.foldr_nil]
  refine WP.seq (WP.mono h0 fun u0 hu0 => ?_)
  refine WP.seq (WP.mono (hk 0 (by decide) u0 hu0) fun u1 hu1 => WP.seq (WP.mono hu1 fun v1 hv1 => ?_))
  refine WP.seq (WP.mono (hk 1 (by decide) v1 hv1) fun u2 hu2 => WP.seq (WP.mono hu2 fun v2 hv2 => ?_))
  refine WP.seq (WP.mono (hk 2 (by decide) v2 hv2) fun u3 hu3 => WP.seq (WP.mono hu3 fun v3 hv3 => ?_))
  refine WP.seq (WP.mono (hk 3 (by decide) v3 hv3) fun u4 hu4 => WP.seq (WP.mono hu4 fun v4 hv4 => ?_))
  exact WP.block_nil hv4

/-- A group of lines storing into `a`. -/
theorem groupQ_ok {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) (a : Arr) {ls : List Impl.Cast5.Line} (hg : GroupOk (some a) ls) :
    WP isa (lines4 ls (storeQuad a)) s fun u =>
      KS m0 S K u (runQ a ls 4 st) ws ∧ u.syms = s.syms ∧ Keep lineRegs s u := by
  refine WP.mono (lines4_ok (fun k u => KS m0 S K u (runQ a ls k st) ws ∧
      Extras u.mem (S.setWidth 64) (exVal st (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ∧
      u.syms = s.syms ∧ Keep lineRegs s u)
    (extras_ok h (hg.2 0 (by decide)) (hg.2 1 (by decide)) (hg.2 2 (by decide)) (hg.2 3 (by decide)))
    fun k hk u ⟨hu, uE, usy, uk⟩ => ?_) fun u ⟨hu, _, usy, uk⟩ => ⟨hu, usy, uk⟩
  obtain ⟨hok, hex, hna⟩ := hg.1 k hk
  have he := lineOk_extra hok
  refine WP.mono (lineQ_ok hu uE hok ?_ a hk) fun v hv => WP.mono hv fun w ⟨hw, wE, wsy, wk⟩ => ?_
  · rw [exVal_sbox _ _ he.1 he.2, hex, get_runQ _ _ _ _ fun e => hna (by rw [e])]
  · rw [runQ_succ]
    exact ⟨hw, wE, by rw [wsy, usy], uk.trans wk⟩

/-- A group of lines storing subkeys `b … b + 3` from `edi`, at `K + 64 hh`. -/
theorem groupK_ok {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) {ls : List Impl.Cast5.Line} (hg : GroupOk none ls) {b hh : Nat} {E : BitVec 32}
    (hdi : s.gpr .edi = E) (hE : ∀ k < 16, addr E (4 * k) = K + BitVec.ofNat 64 (64 * hh + 4 * k))
    (hlen : ws.length = 16 * hh + b) (hle : ws.length + 4 ≤ 32) (hb : b + 4 ≤ 16) :
    WP isa (lines4 ls fun k => storeKey (b + k)) s fun u =>
      KS m0 S K u st (ws ++ keys4 ls st) ∧ u.syms = s.syms ∧ Keep lineRegs s u := by
  refine WP.mono (lines4_ok (fun k u => KS m0 S K u st (ws ++ (keys4 ls st).take k) ∧
      Extras u.mem (S.setWidth 64) (exVal st (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ∧
      u.syms = s.syms ∧ Keep lineRegs s u)
    (WP.mono (extras_ok h (hg.2 0 (by decide)) (hg.2 1 (by decide)) (hg.2 2 (by decide))
      (hg.2 3 (by decide))) fun u ⟨hu, uE, usy, uk⟩ => ⟨by rw [List.take_zero, List.append_nil]; exact hu,
        uE, usy, uk⟩)
    fun k hk u ⟨hu, uE, usy, uk⟩ => ?_) fun u ⟨hu, _, usy, uk⟩ => ⟨hu, usy, uk⟩
  obtain ⟨hok, hex, _⟩ := hg.1 k hk
  have he := lineOk_extra hok
  have hl : (ws ++ (keys4 ls st).take k).length = ws.length + k := by
    rw [List.length_append, List.length_take, show (keys4 ls st).length = 4 from rfl, Nat.min_eq_left (by omega_arith)]
  refine WP.mono (lineK_ok hu uE hok ?_ (k := b + k) (by rw [uk.gpr .edi (by decide), hdi])
      (by rw [hE _ (by omega_arith), hl, hlen]; congr 2; omega_arith) (by rw [hl]; omega_arith))
    fun v hv => WP.mono hv fun w ⟨hw, wE, wsy, wk⟩ => ?_
  · rw [exVal_sbox _ _ he.1 he.2, hex]
  · rw [take_keys4 _ _ hk, ← List.append_assoc]
    exact ⟨hw, wE, by rw [wsy, usy], uk.trans wk⟩

end VG.Proof.Cast5.X86

end

end

/-! ### `Cast5.X86.KeyHalf`, which only this module used -/

section

/-!
# CAST5 key expansion on 32-bit x86: a half

`half` runs the eight groups of lines of §2.4 (`halfImpl`), writing sixteen
subkeys from `edi`, then moves `edi` on and counts the half (`half_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86
open VG.Proof.Cast5 (XZ GroupOk keys4 runQ_z runQ_x halfImpl runZ runX)

theorem gZ : GroupOk (some .z) zLines := by unfold GroupOk; decide
theorem gX : GroupOk (some .x) xLines := by unfold GroupOk; decide
theorem gA : GroupOk none aLines := by unfold GroupOk; decide
theorem gB : GroupOk none bLines := by unfold GroupOk; decide
theorem gC : GroupOk none cLines := by unfold GroupOk; decide
theorem gD : GroupOk none dLines := by unfold GroupOk; decide

theorem storeKey_zero : (fun k => storeKey (0 + k)) = storeKey := funext fun k => by rw [Nat.zero_add]

/-- The registers key expansion's halves write. -/
def keyRegs : List Reg := [.eax, .ecx, .edx, .ebp, .edi, .ebx]

theorem half_ok {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) {hh : Nat} {K32 : BitVec 32} (hK : K = K32.setWidth 64)
    (hfitK : K32.toNat + 128 ≤ 2 ^ 32) (hdi : s.gpr .edi = K32 + BitVec.ofNat 32 (64 * hh))
    (hlen : ws.length = 16 * hh) (hle : hh < 2) :
    WP isa half s fun u =>
      KS m0 S K u (halfImpl st).2 (ws ++ (halfImpl st).1) ∧
      u.gpr .edi = K32 + BitVec.ofNat 32 (64 * (hh + 1)) ∧ u.gpr .ebx = s.gpr .ebx - 1 ∧
      u.zf = some (s.gpr .ebx - 1 == 0) ∧ u.syms = s.syms ∧ Keep keyRegs s u := by
  have kd {u v : State} (k : Keep lineRegs u v) : v.gpr .edi = u.gpr .edi := k.gpr _ (by decide)
  have l4 (ls : List Impl.Cast5.Line) (t : XZ) : (keys4 ls t).length = 4 := rfl
  obtain hE : ∀ k < 16, addr (K32 + BitVec.ofNat 32 (64 * hh)) (4 * k) = K + BitVec.ofNat 64 (64 * hh + 4 * k) := by
    intro k hk
    rw [hK, show addr (K32 + BitVec.ofNat 32 (64 * hh)) (4 * k) = addr K32 (64 * hh + 4 * k) by
      simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact addr_eq (by omega_using [hfitK, hle, hk])
  unfold half
  refine WP.seq (WP.mono (groupQ_ok h .z gZ) fun u1 ⟨h1, s1, k1⟩ => ?_)
  rw [runQ_z] at h1
  obtain g2 := groupK_ok h1 gA (b := 0) (hh := hh) (by rw [kd k1, hdi]) hE (by rw [hlen]; rfl) (by omega_using [hlen, hle]) (by omega_using [])
  rw [storeKey_zero] at g2
  refine WP.seq (WP.mono g2 fun u2 ⟨h2, s2, k2⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h2 .x gX) fun u3 ⟨h3, s3, k3⟩ => ?_)
  rw [runQ_x] at h3
  obtain g4 := groupK_ok h3 gB (b := 4) (hh := hh) (by rw [kd k3, kd k2, kd k1, hdi]) hE
    (by rw [List.length_append, hlen, l4]) (by rw [List.length_append, hlen, l4]; omega_using [hle]) (by omega_using [])
  refine WP.seq (WP.mono g4 fun u4 ⟨h4, s4, k4⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h4 .z gZ) fun u5 ⟨h5, s5, k5⟩ => ?_)
  rw [runQ_z] at h5
  obtain g6 := groupK_ok h5 gC (b := 8) (hh := hh) (by rw [kd k5, kd k4, kd k3, kd k2, kd k1, hdi]) hE
    (by rw [List.length_append, List.length_append, hlen, l4, l4])
    (by rw [List.length_append, List.length_append, hlen, l4, l4]; omega_using [hle]) (by omega_using [])
  refine WP.seq (WP.mono g6 fun u6 ⟨h6, s6, k6⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h6 .x gX) fun u7 ⟨h7, s7, k7⟩ => ?_)
  rw [runQ_x] at h7
  obtain g8 := groupK_ok h7 gD (b := 12) (hh := hh)
    (by rw [kd k7, kd k6, kd k5, kd k4, kd k3, kd k2, kd k1, hdi]) hE
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4]; omega_using [hle]) (by omega_using [])
  refine WP.seq (WP.mono g8 fun u8 ⟨h8, s8, k8⟩ => ?_)
  obtain k18 := (((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8)
  obtain hdi8 : u8.gpr .edi = K32 + BitVec.ofNat 32 (64 * hh) := by rw [k18.gpr _ (by decide), hdi]
  obtain hbx8 : u8.gpr .ebx = s.gpr .ebx := k18.gpr _ (by decide)
  crun [hdi8, hbx8]
  have hst : (halfImpl st).2 = runX xLines (runZ zLines (runX xLines (runZ zLines st))) := rfl
  obtain hks : ws ++ (halfImpl st).1 = ws ++ keys4 aLines (runZ zLines st) ++
      keys4 bLines (runX xLines (runZ zLines st)) ++ keys4 cLines (runZ zLines (runX xLines (runZ zLines st))) ++
      keys4 dLines (runX xLines (runZ zLines (runX xLines (runZ zLines st)))) := by
    simp only [halfImpl, List.append_assoc]
  rw [hst, hks]
  refine ⟨h8.update rfl rfl h8.mem h8.len rfl rfl rfl, ?_, ?_, rfl, by rw [s8, s7, s6, s5, s4, s3, s2, s1],
    fun r hr => ?_, k18.rd, k18.wr⟩
  · rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ]
  · rfl
  · have hr' := hr
    simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain hl : r ∉ lineRegs := by
      simp only [lineRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1⟩
    simp only [gpr_setReg, gpr_arithFlags, hr'.2.2.2.2.1, hr'.2.2.2.2.2, ite_false]
    exact k18.gpr r hl

end VG.Proof.Cast5.X86

end

end


/-!
# CAST5 key expansion on 32-bit x86

`expandKey` saves the callee-saved registers in the working space, pads the
key with zeros into `x` (§2.5), runs both halves of §2.4 and restores the
registers (`key_correct`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86
open VG.Proof.Cast5 (XZ HoldsXZ Keys KMem off_lt halves halves_length halves_two bytesAt_getD scheduleAt_keys
  byte_write Held)

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_byte32 (m : Mem) (c : Addr) {d e : Nat} (hd : d + 4 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (0 : BitVec 32)) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 4 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

/-- The memory after `x` := zeros. -/
def zeroMem (m : Mem) (S : BitVec 32) : Mem :=
  (((m.writeW (addr S xOff) (0 : BitVec 32)).writeW (addr S (xOff + 4)) (0 : BitVec 32)).writeW
    (addr S (xOff + 8)) (0 : BitVec 32)).writeW (addr S (xOff + 12)) (0 : BitVec 32)

theorem zeroMem_cinv (m : Mem) {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) (key : Addr) :
    CInv m key (S.setWidth 64) 0 (zeroMem m S) := by
  have e (d : Nat) (hd : d < 256) := addr_off hfit d hd
  simp only [zeroMem, xOff]
  rw [e 16 (by decide), e 20 (by decide), e 24 (by decide), e 28 (by decide)]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [zero_byte32 _ _ (by decide) (by omega_using [hi]), zero_byte32 _ _ (by decide) (by omega_using [hi]),
      zero_byte32 _ _ (by decide) (by omega_using [hi]), zero_byte32 _ _ (by decide) (by omega_using [hi])]
    repeat' split
    all_goals first | rfl | omega
  · rw [zero_byte32 _ _ (by decide) (by omega_using [hi]), zero_byte32 _ _ (by decide) (by omega_using [hi]),
      zero_byte32 _ _ (by decide) (by omega_using [hi]), zero_byte32 _ _ (by decide) (by omega_using [hi]), ite_eq_right (by omega_using []),
      ite_eq_right (by omega_using []), ite_eq_right (by omega_using []), ite_eq_right (by omega_using [])]
  · exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))

theorem copyStep_ok (u : State) {m0 : Mem} {key c : Addr} {k32 x32 : BitVec 32} {j : Nat} (hj : j < 16)
    (hI : CInv m0 key c j u.mem) (hdi : u.gpr .edi = k32) (hax : u.gpr .eax = x32)
    (ek : addr k32 0 = key + BitVec.ofNat 64 j) (ex : addr x32 0 = c + BitVec.ofNat 64 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (key + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (c + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (key + BitVec.ofNat 64 j) = m0 (key + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 key c (j + 1) v.mem ∧ v.gpr .edi = k32 + 1 ∧ v.gpr .eax = x32 + 1 ∧ v.gpr .ebx = u.gpr .ebx - 1 ∧
      v.zf = some (u.gpr .ebx - 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ebx → r ≠ .ecx → v.gpr r = u.gpr r) ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms := by
  unfold copyStep
  crun [hdi, hax, ek, ex, hr, hw, hk]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, rfl, rfl, rfl, rfl, fun r h1 h2 h3 h4 => ?_⟩
  · simp only [Mem.writeW]
    rw [byte_write (d := 16 + j) (e := 16 + i) (n := 1) _ _ _ (by omega_using [hj]) (by omega_using [hi])]
    split
    · have hij : i = j := by omega_arith
      subst hij
      rw [Nat.sub_self, ite_eq_left (show i < i + 1 by omega_using []), ite_eq_left (show Reg8.cl.reg = Reg.ecx from rfl)]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [hk]
    · rw [hI.x i hi]
      split <;> split <;> first | rfl | omega
  · simp only [Mem.writeW]
    rw [byte_write (d := 16 + j) (e := 32 + i) (n := 1) _ _ _ (by omega_using [hj]) (by omega_using [hi]), ite_eq_right (by omega_using [hj])]
    exact hI.z i hi
  · exact hI.fr.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
  · simp only [h1, h2, h3, h4, ite_false]

/-- The facts of key expansion's precondition on this target (the shared
contract's, `Spec.Cast5.expandKeyContract`, with the table `VG_CAST5_S5678`):
the arguments (`key`, `key_len`, `schedule`, `scratch`) on the stack. -/
structure KPre (s : State) : Prop where
  rdEq : s.rd = [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩,
    ⟨(s.syms s5678Sym).setWidth 64, 4096⟩]
  wrEq : s.wr = [⟨(arg s 2).setWidth 64, 128⟩, ⟨(arg s 3).setWidth 64, 256⟩]
  sp : 4 ≤ (s.gpr .esp).toNat
  spfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  fitk : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  fitK : (arg s 2).toNat + 128 ≤ 2 ^ 32
  fitS : (arg s 3).toNat + 256 ≤ 2 ^ 32
  fitT : (s.syms s5678Sym).toNat + 4096 ≤ 2 ^ 32
  held : Held s.mem ((s.syms s5678Sym).setWidth 64) s5678
  dkK : Region.Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dkS : Region.Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ⟨(arg s 3).setWidth 64, 256⟩
  dKS : Region.Disjoint ⟨(arg s 2).setWidth 64, 128⟩ ⟨(arg s 3).setWidth 64, 256⟩
  dTK : Region.Disjoint ⟨(s.syms s5678Sym).setWidth 64, 4096⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dTS : Region.Disjoint ⟨(s.syms s5678Sym).setWidth 64, 4096⟩ ⟨(arg s 3).setWidth 64, 256⟩
  dAK : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dAS : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 3).setWidth 64, 256⟩
  dRK : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dRS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 3).setWidth 64, 256⟩
  dK : Region.Disjoint ⟨(arg s 2).setWidth 64, 128⟩ (below (s.gpr .esp) 4)
  dS : Region.Disjoint ⟨(arg s 3).setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  dT : Region.Disjoint ⟨(s.syms s5678Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  len : 5 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 16

/-- Key expansion's contract on x86, as its proof states it. -/
def keyX : Contract isa where
  pre s := KPre s
  post s s' := Spec.Cast5.scheduleAt s'.mem ((arg s 2).setWidth 64) =
    Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 4, arg s₁ i = arg s₂ i) ∧ s₁.syms s5678Sym = s₂.syms s5678Sym

/-- The registers key expansion saves. -/
def keySavedL : List (Reg × Nat) := [(.ebx, keySavedOff), (.edi, keySavedOff + 8), (.ebp, keySavedOff + 12)]

theorem keySaved_eq : keySaved = keySavedL ++ [(.esi, keySavedOff + 4)] := rfl
theorem keyRestore_eq : keyRestore = Spill.restoreCode .esi keySaved := rfl
theorem keySave_eq : keySave = Spill.saveCode .eax keySaved := rfl
theorem keySaved_fits : Spill.Fits 256 keySaved := by decide

theorem keySaved_contains {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) :
    ∀ p ∈ keySaved, Region.Contains (slotR S 64 16) (addr S p.2) 4 := by
  intro p hp
  simp only [keySaved, keySavedOff, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
  · rw [addr_off hfit _ (by decide)]; exact Offset.contains _ (by decide) (by decide) (by decide)

theorem keySaved_in {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) :
    ∀ p ∈ keySaved, Region.Contains ⟨S.setWidth 64, 256⟩ (addr S p.2) 4 := by
  intro p hp
  simp only [keySaved, keySavedOff, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
  · rw [addr_off hfit _ (by decide)]; exact Offset.contains_base _ (by decide) (by decide)

theorem argK_in {s : State} (h : KPre s) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  obtain hA : InRegions (s.rd ++ s.wr) (argAddr s 0) 16 := by
    rw [h.rdEq]; exact ⟨_, by simp, Region.contains_self _ _⟩
  obtain e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by have := h.spfit; omega_using [this])
  rw [e0] at hA
  rw [addr_eq (by have := h.spfit; omega_using [hi, this]), ← Offset.add_add]
  exact CallLay.inRegions_sub hA (by omega_using [hi]) (by decide)

theorem one32 : (1 : BitVec 32) = BitVec.ofNat 32 1 := rfl

theorem addr_shift (x : BitVec 32) (a : Nat) : addr (x + BitVec.ofNat 32 a) 0 = addr x a :=
  congrArg (BitVec.setWidth 64) (BitVec.add_zero _)

theorem key_correct (s : State) (h : KPre s) :
    WP isa expandKey s fun s' => abiPreserved s s' ∧ keyX.post s s' := by
  obtain ⟨kk, hkk⟩ : ∃ x, arg s 0 = x := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ x, arg s 1 = x := ⟨_, rfl⟩
  obtain ⟨K32, hK32⟩ : ∃ x, arg s 2 = x := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ x, arg s 3 = x := ⟨_, rfl⟩
  obtain fitS : S.toNat + 256 ≤ 2 ^ 32 := hS ▸ h.fitS
  obtain fitK : K32.toNat + 128 ≤ 2 ^ 32 := hK32 ▸ h.fitK
  obtain fitk : kk.toNat + L.toNat ≤ 2 ^ 32 := hkk ▸ hL ▸ h.fitk
  obtain hlen : 5 ≤ L.toNat ∧ L.toNat ≤ 16 := hL ▸ h.len
  obtain wS : InRegions s.wr (S.setWidth 64) 256 := by rw [h.wrEq, hS]; exact ⟨_, by simp, Region.contains_self _ _⟩
  obtain wK : InRegions s.wr (K32.setWidth 64) 128 := by
    rw [h.wrEq, hK32]; exact ⟨_, by simp, Region.contains_self _ _⟩
  obtain rk : InRegions (s.rd ++ s.wr) (kk.setWidth 64) L.toNat := by
    rw [h.rdEq, hkk, hL]; exact ⟨_, by simp, Region.contains_self _ _⟩
  obtain a0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := argK_in h (i := 0) (by decide)
  obtain a1 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := argK_in h (i := 1) (by decide)
  obtain a2 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4 := argK_in h (i := 2) (by decide)
  obtain a3 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4 := argK_in h (i := 3) (by decide)
  have v3 : s.mem.readW (addr (s.gpr .esp) 16) 32 = S := hS
  -- The saved registers' memory.
  let g := (s.setReg .eax S).gpr
  let SM := Spill.saveMem s.mem (addr S) g keySaved
  obtain fSM : Frame [⟨S.setWidth 64, 256⟩] s.mem SM :=
    Spill.saveMem_frame List.mem_cons_self (addr S) g keySaved s.mem (keySaved_in fitS)
  have argSM (i : Nat) (hi : i < 3) : SM.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := by
    refine Spill.saveMem_readW_of_sep _ _ (by decide) keySaved s.mem fun p hp => ?_
    refine Region.Disjoint.sep (h.dAS) ?_ ?_
    · have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by have := h.spfit; omega_arith)
      rw [addr_eq (by have := h.spfit; omega_arith), e0, ← Offset.add_add]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · rw [hS]; exact keySaved_in fitS p hp
  obtain sk : SM.readW (addr (s.gpr .esp) 4) 32 = kk := (argSM 0 (by decide)).trans hkk
  obtain sl : SM.readW (addr (s.gpr .esp) 8) 32 = L := (argSM 1 (by decide)).trans hL
  obtain sK : SM.readW (addr (s.gpr .esp) 12) 32 = K32 := (argSM 2 (by decide)).trans hK32
  obtain w16 := slot_wr (s := s) fitS wS (d := xOff) (n := 4) (by decide)
  obtain w20 := slot_wr (s := s) fitS wS (d := xOff + 4) (n := 4) (by decide)
  obtain w24 := slot_wr (s := s) fitS wS (d := xOff + 8) (n := 4) (by decide)
  obtain w28 := slot_wr (s := s) fitS wS (d := xOff + 12) (n := 4) (by decide)
  unfold expandKey
  rw [List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain h1 : WP isa (.block [.mov .eax (.mem (at_ .esp 16))]) s fun s₁ => s₁ = s.setReg .eax S := by
    crun [a3, v3]
  refine WP.mono h1 fun s₁ e₁ => ?_
  subst e₁
  rw [keySave_eq]
  refine Spill.save_ok keySaved (fun p hp => ?_) fun s₂ u₂ => ?_
  · rw [wr_setReg, gpr_setReg_self]
    exact slot_wr fitS wS (d := p.2) (n := 4) (by have := keySaved_fits.1 p hp; omega_arith)
  have g₂ : s₂.gpr = g := u₂.gpr
  obtain m₂ : s₂.mem = SM := by rw [u₂.mem]; rfl
  have rd₂ : s₂.rd = s.rd := u₂.rd
  have wr₂ : s₂.wr = s.wr := u₂.wr
  have sy₂ : s₂.syms = s.syms := u₂.syms
  obtain hge : g .eax = S := gpr_setReg_self _ _ _
  obtain hgsp : g .esp = s.gpr .esp := gpr_setReg_of_ne _ _ (by decide)
  obtain hsetup : WP isa (.block keySetup) s₂ fun s₃ => s₃.mem = zeroMem SM S ∧ s₃.gpr .esi = S ∧
      s₃.gpr .edi = kk ∧ s₃.gpr .ebx = L ∧ s₃.gpr .edx = K32 ∧ s₃.gpr .eax = S + BitVec.ofNat 32 16 ∧
      s₃.gpr .esp = s.gpr .esp ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧ s₃.syms = s.syms := by
    unfold keySetup
    crun [g₂, m₂, rd₂, wr₂, sy₂, hge, hgsp, a0, a1, a2, sk, sl, sK, w16, w20, w24, w28]
    exact ⟨rfl, rfl⟩
  refine WP.mono hsetup fun s₃ ⟨m₃, si₃, di₃, bx₃, dx₃, ax₃, sp₃, rd₃, wr₃, sy₃⟩ => ?_
  obtain dkS64 : Region.Disjoint ⟨kk.setWidth 64, L.toNat⟩ ⟨S.setWidth 64, 64⟩ := by
    have := h.dkS; rw [hkk, hL, hS] at this; exact this.sub_right (Region.sub_prefix (by decide))
  have hkb (j : Nat) (hj : j < L.toNat) (m : Mem) (hf : Frame [⟨S.setWidth 64, 64⟩] SM m) :
      m (kk.setWidth 64 + BitVec.ofNat 64 j) = SM (kk.setWidth 64 + BitVec.ofNat 64 j) := by
    refine hf.bytes (R := ⟨kk.setWidth 64, L.toNat⟩) (fun r hr => ?_) (by show L.toNat ≤ 2 ^ 64; omega_arith) hj
    rw [List.mem_singleton] at hr; rw [hr]; exact dkS64
  refine WP.seq (wp_countdown (cnt := .ebx) (N := L.toNat) (by omega_arith) (by omega_arith)
    (fun j u => CInv SM (kk.setWidth 64) (S.setWidth 64) j u.mem ∧ u.gpr .edi = kk + BitVec.ofNat 32 j ∧
      u.gpr .eax = S + BitVec.ofNat 32 (16 + j) ∧
      (∀ r, r ∉ [Reg.eax, .edi, .ebx, .ecx] → u.gpr r = s₃.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms)
    (fun j hj u ⟨cu, du, au, gu, rdu, wru, syu⟩ _ => WP.mono (copyStep_ok u (by omega_arith) cu du au
      (by rw [addr_shift]; exact addr_eq (by omega_arith))
      (by rw [addr_shift]; exact addr_eq (by omega_arith))
      (by rw [rdu, wru]; exact CallLay.inRegions_sub rk (by omega_arith) (by omega_arith))
      (by rw [wru]; exact CallLay.inRegions_sub wS (by omega_arith) (by decide))
      (hkb j hj u.mem cu.fr))
      fun v ⟨cv, dv, av, sv, zv, gv, rdv, wrv, syv⟩ => ⟨⟨cv, by rw [dv, one32, add_ofNat_add32 _ j 1], by
        rw [av, one32, add_ofNat_add32 _ (16 + j) 1, Nat.add_assoc], fun r hr => ?keepStep, rdv.trans rdu, wrv.trans wru,
        syv.trans syu⟩, sv, zv⟩)
    (fun u hu => ?rest)
    ⟨by rw [m₃]; exact zeroMem_cinv SM fitS _, by rw [di₃]; exact (BitVec.add_zero _).symm, by rw [ax₃],
      fun _ _ => rfl, rd₃, wr₃, sy₃⟩ (by rw [bx₃, ofNat_toNat32]))
  case keepStep =>
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [gv r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2, gu r hr]
  case rest =>
    obtain ⟨cu, -, -, gu, rdu, wru, syu⟩ := hu
    obtain hsi_u : u.gpr .esi = S := (gu .esi (by decide)).trans si₃
    obtain hdx_u : u.gpr .edx = K32 := (gu .edx (by decide)).trans dx₃
    obtain hsp_u : u.gpr .esp = s.gpr .esp := (gu .esp (by decide)).trans sp₃
    refine WP.seq (WP.mono (show WP isa (.block [.mov .edi (.reg .edx), .mov .ebx (imm 2)]) u fun v =>
        v.gpr .edi = K32 ∧ v.gpr .ebx = BitVec.ofNat 32 2 ∧ v.mem = u.mem ∧
          (∀ r, r ≠ .edi → r ≠ .ebx → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms by
      crun [hdx_u]
      exact fun r h1 h2 => by simp only [h1, h2, ite_false]) fun u1 ⟨di1, bx1, m1, g1, rd1, wr1, sy1⟩ => ?_)
    obtain si1 : u1.gpr .esi = S := (g1 .esi (by decide) (by decide)).trans hsi_u
    obtain sp1 : u1.gpr .esp = s.gpr .esp := (g1 .esp (by decide) (by decide)).trans hsp_u
    obtain rd1' : u1.rd = s.rd := rd1.trans rdu
    obtain wr1' : u1.wr = s.wr := wr1.trans wru
    obtain sy1' : u1.syms = s.syms := sy1.trans syu
    -- The memory so far: only the working space written.
    obtain fU : Frame [⟨S.setWidth 64, 256⟩] s.mem u1.mem := by
      rw [m1]
      exact fSM.trans (cu.fr.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩)
    obtain dSK : Region.Disjoint ⟨K32.setWidth 64, 128⟩ ⟨S.setWidth 64, 256⟩ := by rw [← hK32, ← hS]; exact h.dKS
    obtain dTS : Region.Disjoint ⟨(s.syms s5678Sym).setWidth 64, 4096⟩ ⟨S.setWidth 64, 256⟩ := by
      rw [← hS]; exact h.dTS
    -- The arrays after the copy.
    let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem (kk.setWidth 64) L.toNat).getD j 0,
      fun j => u1.mem (S.setWidth 64 + BitVec.ofNat 64 (32 + j))⟩
    obtain xz0 : HoldsXZ u1.mem (S.setWidth 64) st0 := by
      intro a i hi
      cases a with
      | x =>
        rw [show off .x + i = 16 + i from rfl, m1, cu.x i hi]
        show _ = (Spec.Cast5.bytesAt s.mem (kk.setWidth 64) L.toNat).getD i 0
        rw [bytesAt_getD]
        split
        · rw [fSM.bytes (R := ⟨kk.setWidth 64, L.toNat⟩) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; rw [← hkk, ← hL, ← hS]; exact h.dkS)
            (by show L.toNat ≤ 2 ^ 64; omega_arith) (by assumption)]
        · rfl
      | z => rfl
    obtain held0 : Held u1.mem ((s.syms s5678Sym).setWidth 64) s5678 := by
      intro i hi
      rw [s5678_length] at hi
      rw [fU.readW (r := ⟨(s.syms s5678Sym).setWidth 64, 4096⟩)
        (Offset.contains_base _ (by omega_arith) (by have := h.fitT; omega_arith))
        (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dTS) (by decide)]
      exact h.held i (by rw [s5678_length]; exact hi)
    obtain ks0 : KS u1.mem S (K32.setWidth 64) u1 st0 [] := by
      refine ⟨si1, fitS, by rw [wr1']; exact wS, ⟨xz0, fun i hi => absurd hi (Nat.not_lt_zero _), Frame.refl _ _⟩,
        Nat.zero_le _, by rw [wr1']; exact wK, dSK, by rw [sp1]; exact h.sp, by rw [sp1, ← hS]; exact h.dS,
        by rw [sp1, ← hK32]; exact h.dK, by rw [sy1']; exact h.fitT,
        by rw [rd1', wr1', sy1', h.rdEq]; exact ⟨_, by simp, Region.contains_self _ _⟩, ?_, by rw [sy1']; exact held0⟩
      intro r hr
      rw [sy1']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dTS
      · rw [← hK32]; exact h.dTK
      · rw [sp1]; exact h.dT
    refine WP.seq (wp_countdown (cnt := .ebx) (N := 2) (by decide) (by decide)
      (fun hh v => KS u1.mem S (K32.setWidth 64) v (halves st0 hh).1 (halves st0 hh).2 ∧
        v.gpr .edi = K32 + BitVec.ofNat 32 (64 * hh) ∧ v.syms = s.syms ∧ Keep keyRegs u1 v)
      (fun hh hh2 v ⟨kv, dv, syv, kpv⟩ _ => WP.mono (half_ok kv rfl fitK dv (halves_length st0 hh) hh2)
        fun w ⟨kw, dw, sw, zw, syw, kpw⟩ => ⟨⟨kw, dw, syw.trans syv, kpv.trans kpw⟩, sw, zw⟩)
      (fun v hv => ?fin)
      ⟨ks0, by rw [di1]; exact (BitVec.add_zero _).symm, sy1', Keep.refl _ _⟩ bx1)
    case fin =>
      obtain ⟨kv, -, syv, kpv⟩ := hv
      obtain vsi : v.gpr .esi = S := (kpv.gpr .esi (by decide)).trans si1
      obtain vsp : v.gpr .esp = s.gpr .esp := (kpv.gpr .esp (by decide)).trans sp1
      obtain vrd : v.rd = s.rd := kpv.rd.trans rd1'
      obtain vwr : v.wr = s.wr := kpv.wr.trans wr1'
      -- The saved registers.
      obtain hs0 : Spill.Saved SM (addr S) g keySaved := Spill.saveMem_saved_addr s.mem g keySaved_fits fitS
      obtain d64 : Region.Disjoint (slotR S 64 16) ⟨S.setWidth 64, 64⟩ :=
        Offset.disjoint_base _ (by decide) (by decide)
      obtain hs1 : Spill.Saved u1.mem (addr S) g keySaved := by
        rw [m1]
        exact hs0.of_frame cu.fr (keySaved_contains fitS) fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact d64
      obtain hs2 : Spill.Saved v.mem (addr S) g keySaved := by
        refine hs1.of_frame kv.mem.fr (keySaved_contains fitS) fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact d64
        · exact (dSK.symm).sub_left (slot_sub S (by decide))
        · rw [vsp, ← hS]; exact h.dS.sub_left (by rw [hS]; exact slot_sub S (by decide))
      rw [keyRestore_eq, keySaved_eq, ← List.append_nil (Spill.restoreCode _ _)]
      refine Spill.restoreBase_ok keySavedL (by decide) (fun p hp => ?_) (by rw [vsi, ← keySaved_eq]; exact hs2)
        fun s' hr => WP.block_nil ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
      · rw [vsi, vrd, vwr]
        rw [← keySaved_eq] at hp
        exact slot_rd fitS wS (d := p.2) (n := 4) (by have := keySaved_fits.1 p hp; omega_arith)
      · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl
        · exact (hr.gpr (.ebx, keySavedOff) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.gpr (.esi, keySavedOff + 4) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.gpr (.edi, keySavedOff + 8) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.gpr (.ebp, keySavedOff + 12) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.other .esp (by decide)).trans vsp
      · have dR : ∀ r ∈ ([⟨S.setWidth 64, 64⟩, ⟨K32.setWidth 64, 128⟩, below (v.gpr .esp) 4] : List Region),
            Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r := by
          intro r hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl | rfl
          · exact (show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨S.setWidth 64, 256⟩ by
              rw [← hS]; exact h.dRS).sub_right (Region.sub_prefix (by decide))
          · rw [← hK32]; exact h.dRK
          · rw [vsp, below, Taint.sub_setWidth h.sp]
            exact Offset.base_disjoint_below _ (by decide)
        rw [hr.mem, kv.mem.fr.readW (Region.contains_self _ _) dR (by decide),
          fU.readW (Region.contains_self _ _) (fun r hr' => by
            rw [List.mem_singleton] at hr'; subst hr'; rw [← hS]; exact h.dRS) (by decide)]
      · show Spec.Cast5.scheduleAt s'.mem _ = _
        rw [hr.mem, hK32, hkk, hL, scheduleAt_keys kv.mem.keys (halves_length st0 2),
          Proof.Cast5.expandKey_eq _ st0.z, halves_two]

end VG.Proof.Cast5.X86

end

end

/-!
# CAST5 key expansion on 32-bit x86: verified against the shared contract

Constant time by the taint analysis: `esp`, the arguments on the stack (the
working space's address among them) and the table's address are public; the
key's length decides the number of bytes copied.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.Impl.Cast5.X86
open VG.Impl.Cast5 (s5678Sym s5678 keyConsts)

/-- The initial taint: `esp`, the 16 bytes of arguments (the fourth, the base
of writable region 1, the working space) and the 4 bytes of stack below `esp`
outside every writable region. -/
def τKey : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128, 256], argLen := 20, argBases := [(16, 1)], room := 4 }

theorem τKey_wf {s : State} (h : keyX.pre s) : VG.X86.Taint.Wf τKey s := by
  have hw := h.wrEq
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨h.spfit, ?_⟩, ?_⟩ ?_
  · rw [hw]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
      and_true]
    exact ⟨h.dKS, fun _ h => h.elim⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simp only [toNat_setWidth]; exact h.fitK
    · simp only [toNat_setWidth]; exact h.fitS
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := h.spfit; omega_using [this]) h.dRK h.dAK
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := h.spfit; omega_using [this]) h.dRS h.dAS
  · intro p hp
    simp only [τKey, List.mem_singleton] at hp
    subst hp
    refine ⟨by decide, ?_⟩
    simp only [VG.X86.Taint.region, hw]
    show addr (arg s 3) 0 = _
    rw [addr_off h.fitS 0 (by decide), BitVec.add_zero]
    rfl
  · intro _
    refine ⟨h.sp, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 = (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 :=
      (VG.X86.Taint.sub_setWidth h.sp).symm
    simp only [τKey]
    rw [e]
    simp only [hw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.dK.symm
    · exact h.dS.symm

theorem τKey_agree {s₁ s₂ : State} (h₁ : keyX.pre s₁) (h₂ : keyX.pre s₂) (hp : keyX.pub s₁ s₂) :
    VG.X86.Taint.AgreeS [s5678Sym] τKey s₁ s₂ := by
  obtain ⟨sp, args, sy⟩ := hp
  refine ⟨⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τKey_wf h₁, τKey_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩, fun n hn => ?_⟩
  · simp only [τKey, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [h₁.wrEq, h₂.wrEq, args 2 (by decide), args 3 (by decide)]
  · simp only [τKey] at hk
    rw [show VG.X86.Taint.depth τKey.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := h₁.spfit; omega_using [this]) h4 hk,
      VG.X86.Taint.argByte_eq (by have := h₂.spfit; omega_using [this]) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_using [hk]))
  · simp only [List.mem_singleton] at hn
    subst hn
    exact sy

theorem expandKey_ct : ConstantTime isa keyX.pre keyX.pub expandKey :=
  VG.Taint.constantTime (A := taintSym [s5678Sym]) τKey (fun _ _ h₁ h₂ hp => τKey_agree h₁ h₂ hp)
    (by taint_decide)

theorem keyConsts_eq : keyConsts = [(s5678Sym, s5678)] := rfl

theorem key_implies_pre (s : State)
    (h : (Spec.Cast5.expandKeyContract (X86.abi.withConsts keyConsts) 4).pre s) : keyX.pre s := by
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, keyConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s5678_length] at h
  obtain ⟨h4, hsp, hdrop, held, fitT, dTw, -, dTB, -, htake, hwr, dkK, dkS, dKS, dKA, dSA, -, dRK, dRS, -, -, dBK,
    dBS, -, fk, fK, fS, hv⟩ := h
  have be : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
    simp only [below, Taint.sub_setWidth h4]
  have hrd : s.rd = [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩,
      ⟨(s.syms s5678Sym).setWidth 64, 4096⟩] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop]; rfl
  have mK : (⟨(arg s 2).setWidth 64, 128⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mS : (⟨(arg s 3).setWidth 64, 256⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrd
  · exact hwr
  · exact h4
  · exact hsp
  · exact fk
  · exact fK
  · exact fS
  · exact fitT
  · exact fun i hi => held i (by rw [s5678_length] at hi; exact hi)
  · exact dkK
  · exact dkS
  · exact dKS
  · exact dTw _ mK
  · exact dTw _ mS
  · exact dKA.symm
  · exact dSA.symm
  · exact dRK
  · exact dRS
  · rw [be]; exact dBK.symm
  · rw [be]; exact dBS.symm
  · rw [be]; exact dTB
  · exact hv

/-- The arguments of the witness at `0x8004`: a key of 16 bytes at `0x1000`,
the schedule at `0x2000` and the working space at `0x3000`. -/
def keyArgs : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20 else if a = 0x8011 then 0x30
  else 0

/-- The memory of the contract's witness: the table at `0x100000`, the
arguments elsewhere (irreducible: unfolding it in a definitional check would
evaluate the table). -/
@[irreducible] def keySatMem : Mem := fun a =>
  if (a - 0x100000).toNat < 4096 then constMem 0x100000 s5678 a else keyArgs a

theorem keySatMem_held : ∀ i < s5678.length,
    keySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s5678.getD i 0 := by
  intro i hi
  rw [s5678_length] at hi
  have hm : keySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 s5678).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hj])]
    unfold keySatMem
    rw [e, ite_eq_left (show 8 * i + j < 4096 by omega_using [hi, hj])]
  exact hm.trans (constMem_held 0x100000 s5678 (by rw [s5678_length]; decide) i (by rw [s5678_length]; exact hi))

/-- A state satisfying key expansion's precondition. -/
def keySat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := keySatMem
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 16⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 256⟩]
  syms _ := 0x100000

theorem keySat_arg (j : Nat) (hj : j < 4) : arg keySat j = keyArgs.readW (argAddr keySat j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change keySatMem _ = _
  unfold keySatMem
  have : ∀ j < 4, ∀ b < 4, ¬ (argAddr keySat j + BitVec.ofNat 64 b - 0x100000).toNat < 4096 := by decide
  rw [ite_eq_right (this j hj b (by omega_using [hb]))]

theorem key_sat : (Spec.Cast5.expandKeyContract (X86.abi.withConsts keyConsts) 4).pre keySat := by
  have a0 : arg keySat 0 = 0x1000 := (keySat_arg 0 (by decide)).trans (by decide)
  have a1 : arg keySat 1 = 16 := (keySat_arg 1 (by decide)).trans (by decide)
  have a2 : arg keySat 2 = 0x2000 := (keySat_arg 2 (by decide)).trans (by decide)
  have a3 : arg keySat 3 = 0x3000 := (keySat_arg 3 (by decide)).trans (by decide)
  have held := keySatMem_held
  generalize e : keySat = s
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, keyConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s5678_length]
  subst s
  rw [a0, a1, a2, a3]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s5678_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 128⟩, ⟨0x3000, 256⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem key_implies : keyX.Implies (Spec.Cast5.expandKeyContract (X86.abi.withConsts keyConsts) 4) where
  pre := key_implies_pre
  post := by
    intro s t _ h
    sig_post [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, keyConsts_eq, Abi.withConsts]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, keyConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2, h3⟩ := h
    refine ⟨hsp, fun i hi => ?_, hsy⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  sat := ⟨keySat, key_sat⟩

theorem keyX_correct (s : State) (hs : keyX.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyX.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_correct s hs
  exact ⟨t, s', he, ha, hp⟩

theorem expandKey_verified :
    Verified X86.target expandKey (Spec.Cast5.expandKeyContract (X86.abi.withConsts keyConsts) 4) :=
  Verified.of_correct keyX_correct expandKey_ct key_implies

end VG.Proof.Cast5.X86
