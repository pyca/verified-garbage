module

public import VerifiedGarbage.Impl.Cast5.X86_64
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Cast5.KeyMem
public import VerifiedGarbage.Proof.Cast5.X86_64.Block
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! ### `Cast5.X86_64.KeyLine`, which only this module used -/

section

/-!
# CAST5 key expansion on x86-64: a line

`line l` gathers the line's four main bytes from the working space into the
lanes of `xmm0` (`gather_ok`), scans `VG_CAST5_S5678`, and XORs the four
values, the group's extra lookup and the quadruple, if any (`line_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86_64
open VG.Proof.MlKem.X86_64 (Keep sx_ofNat WP.keep writesOnly)

/-- The index lanes of a gather: the bytes at `d`, `c`, `b`, `a`. -/
def gIdx (m : Mem) (p : Addr) (a b c d : Pos) : Nat → BitVec 32
  | 0 => (m (p + BitVec.ofNat 64 (srcOff d))).setWidth 32
  | 1 => (m (p + BitVec.ofNat 64 (srcOff c))).setWidth 32
  | 2 => (m (p + BitVec.ofNat 64 (srcOff b))).setWidth 32
  | _ => (m (p + BitVec.ofNat 64 (srcOff a))).setWidth 32

theorem setWidth_8_64 (x : BitVec 8) : x.setWidth 64 = (x.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth]
  by_cases h : i < 32
  · simp [h]
  · rw [BitVec.getLsbD_of_ge x i (by omega_using [h])]; simp [h]

theorem gather_ok (s : State) {a b c d : Pos}
    (ha : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (srcOff a)) 1)
    (hb : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (srcOff b)) 1)
    (hc : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (srcOff c)) 1)
    (hd : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (srcOff d)) 1) :
    WP isa (.block (gather a b c d)) s fun u =>
      u.xmm .xmm0 = L (gIdx s.mem (s.gpr .rcx) a b c d) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  unfold gather lanes
  xrun [VG.Proof.Cast5.X86_64.ea_at, ha, hb, hc, hd, XOp.exec, xmm_setReg, xmm_setFlags, gpr_setXmm,
    mem_setXmm, rd_setXmm, wr_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne, List.cons_append, List.nil_append]
  rw [BitVec.or_comm (BitVec.setWidth 64 (s.mem (s.gpr .rcx + BitVec.ofNat 64 (srcOff a))) <<< (32 : Nat)),
    setWidth_8_64 (s.mem _), setWidth_8_64 (s.mem _), setWidth_8_64 (s.mem _),
    setWidth_8_64 (s.mem _), lanes_eq]
  rfl

/-- Bytes `[d, d + n)` of a working space of 64 bytes at `p`. -/
theorem scr_w {s : State} {p : Addr} (h : InRegions s.wr p 64) {d n : Nat} (hd : d + n ≤ 64) :
    InRegions s.wr (p + BitVec.ofNat 64 d) n :=
  CallLay.inRegions_sub h hd (by decide)

theorem scr_rw {s : State} {p : Addr} (h : InRegions s.wr p 64) {d n : Nat} (hd : d + n ≤ 64) :
    InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 d) n := by
  obtain ⟨g, hg, hgc⟩ := scr_w h hd
  exact ⟨g, List.mem_append_right _ hg, hgc⟩

/-- The value a line's last block computes from `v`, the extra lookup `x`
and the memory `m` holding its quadruple. -/
def withWord (m : Mem) (p : Addr) (v : Spec.Cast5.Word) : Option (Arr × Nat) → Spec.Cast5.Word
  | some (a, q) => v ^^^ byteRev32 (m.readW (p + BitVec.ofNat 64 (off a + 4 * q)) 32)
  | none => v

/-- The XORs of a line, after the scan. -/
def tail (e : Nat) (wd : Option (Arr × Nat)) : List Instr :=
  ([.movdquStore (at_ .rcx 0) .xmm1, .mov32 .rax (.mem (at_ .rcx 0)),
    .alu32 .xor .rax (.mem (at_ .rcx 4)), .alu32 .xor .rax (.mem (at_ .rcx 8)),
    .alu32 .xor .rax (.mem (at_ .rcx 12)),
    .alu32 .xor .rax (.mem (at_ .rcx (extraOff + 4 * (8 - e))))] : List Instr) ++
  (match wd with
    | some (a, q) => [.mov32 .r9 (.mem (at_ .rcx (off a + 4 * q))), .bswap32 .r9,
        .alu32 .xor .rax (.reg .r9)]
    | none => [])

theorem line_eq (l : Impl.Cast5.Line) :
    line l = .seq (.block (gather l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2))
      (.seq (scan s5678Sym) (.block (tail l.extra.1 l.word))) := rfl

theorem tail_ok (s : State) {e : Nat} (he : 5 ≤ e) {wd : Option (Arr × Nat)}
    (hq : ∀ a q, wd = some (a, q) → q < 4) {v : Nat → Spec.Cast5.Word} (h1 : s.xmm .xmm1 = L v)
    (hw : InRegions s.wr (s.gpr .rcx) 64) :
    WP isa (.block (tail e wd)) s fun u =>
      u.gpr .rax = (withWord s.mem (s.gpr .rcx) (v 0 ^^^ v 1 ^^^ v 2 ^^^ v 3 ^^^
        s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 (extraOff + 4 * (8 - e))) 32) wd).setWidth 64 ∧
      u.mem = s.mem.writeW (s.gpr .rcx) (L v) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms := by
  have e0 : InRegions (s.rd ++ s.wr) (s.gpr .rcx) 4 := by
    have := scr_rw hw (d := 0) (n := 4) (by decide); rwa [BitVec.add_zero] at this
  have e1 := scr_rw hw (d := 4) (n := 4) (by decide)
  have e2 := scr_rw hw (d := 8) (n := 4) (by decide)
  have e3 := scr_rw hw (d := 12) (n := 4) (by decide)
  have ex := scr_rw hw (d := extraOff + 4 * (8 - e)) (n := 4) (by unfold extraOff; omega_using [he])
  have w0 : InRegions s.wr (s.gpr .rcx) 16 := by
    have := scr_w hw (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this
  have d0 : dword (L v) 0 = v 0 := dword_L v (by decide)
  have d1 : dword (L v) 1 = v 1 := dword_L v (by decide)
  have d2 : dword (L v) 2 = v 2 := dword_L v (by decide)
  have d3 : dword (L v) 3 = v 3 := dword_L v (by decide)
  have sx : (s.mem.writeW (s.gpr .rcx) (L v)).readW
      (s.gpr .rcx + BitVec.ofNat 64 (extraOff + 4 * (8 - e))) 32 =
      s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 (extraOff + 4 * (8 - e))) 32 :=
    Mem.readW_writeW_sep (sep_base' _ (by unfold extraOff; omega_using []) (by unfold extraOff; omega_using []))
      (by decide)
  unfold tail
  cases wd with
  | none =>
    xrun [VG.Proof.Cast5.X86_64.ea_at, State.store128, w0, h1, e0, e1, e2, e3, ex, rd_lane0, rd_lane1,
      rd_lane2, rd_lane3, d0, d1, d2, d3, sx, List.append_nil]
    exact ⟨rfl, rfl⟩
  | some aq =>
    obtain ⟨a, q⟩ := aq
    have hq4 := hq a q rfl
    have eq := scr_rw hw (d := off a + 4 * q) (n := 4) (by have := off_lt a; omega_using [hq4, this])
    have sq : (s.mem.writeW (s.gpr .rcx) (L v)).readW (s.gpr .rcx + BitVec.ofNat 64 (off a + 4 * q)) 32 =
        s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 (off a + 4 * q)) 32 :=
      Mem.readW_writeW_sep (sep_base' _ (by have := off_ge a; omega_using [this])
        (by have := off_lt a; omega_using [hq4, this])) (by decide)
    xrun [VG.Proof.Cast5.X86_64.ea_at, State.store128, w0, h1, e0, e1, e2, e3, ex, eq, rd_lane0, rd_lane1,
      rd_lane2, rd_lane3, d0, d1, d2, d3, sx, sq, List.cons_append, List.nil_append, bswap32_eq]
    exact ⟨rfl, rfl⟩

theorem tail_writes (e : Nat) (wd : Option (Arr × Nat)) :
    writesOnly [.rax, .r9] (.block (tail e wd)) = true := by
  cases wd with
  | none => rfl
  | some aq => obtain ⟨a, q⟩ := aq; rfl

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

/-- A line: `eax` := its value, with only the first 16 bytes of the working
space written. -/
theorem line_ok (s : State) (st : XZ) (l : Impl.Cast5.Line) (hl : lineOk l = true)
    (hw : InRegions s.wr (s.gpr .rcx) 64) (hm : HoldsXZ s.mem (s.gpr .rcx) st)
    (hT : Readable s (s.syms s5678Sym)) (hheld : Held s.mem (s.syms s5678Sym) s5678)
    (hx : s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 (extraOff + 4 * (8 - l.extra.1))) 32 =
      sbox l.extra.1 (st.get l.extra.2)) :
    WP isa (line l) s fun u => u.gpr .rax = (lineVal st l).setWidth 64 ∧
      (∃ w : BitVec 128, u.mem = s.mem.writeW (s.gpr .rcx) w) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      u.syms = s.syms ∧ Keep [.rax, .r9, .r10, .r11] s u := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he5⟩, _⟩, hwd⟩ := hl
  have hin (q : Pos) (hq : q.2 < 16) : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (srcOff q)) 1 :=
    scr_rw hw (by obtain ⟨a', i'⟩ := q; have := off_lt a'; simp only [srcOff] at hq ⊢; omega_using [hq, this])
  rw [line_eq]
  refine WP.seq (WP.mono_syms (WP.keep [.rax, .r9, .r10] (gather_ok s (hin _ ha) (hin _ hb) (hin _ hc)
    (hin _ hd)) (by rfl)) fun u ⟨⟨u0, um, urd, uwr⟩, uk⟩ usy => ?_)
  have hT' : Readable u (u.syms s5678Sym) := by unfold Readable; rw [usy, urd, uwr]; exact hT
  refine WP.seq (WP.mono_syms (scan_ok u s5678Sym u0 (fun k hk => gIdx_lt _ _ _ _ _ _ hk) hT')
    fun v ⟨v1, vk⟩ vsy => ?_)
  have g (r : Reg) (hr : r ∉ [Reg.rax, .r9, .r10]) (h10 : r ≠ .r10) (h11 : r ≠ .r11) : v.gpr r = s.gpr r :=
    (vk.gpr r h10 h11).trans (uk.1 r hr)
  have hrc : v.gpr .rcx = s.gpr .rcx := g .rcx (by decide) (by decide) (by decide)
  have hvw : InRegions v.wr (v.gpr .rcx) 64 := by rw [vk.wr, uwr, hrc]; exact hw
  have hq : ∀ a q, l.word = some (a, q) → q < 4 := by
    intro a q h; rw [h] at hwd; simpa using hwd
  refine WP.mono (WP.keep [.rax, .r9] (tail_ok v he5 hq v1 hvw) (tail_writes _ _))
    fun w ⟨⟨wax, wm, wrd, wwr, wsy⟩, wk⟩ => ?_
  have hvm : v.mem = s.mem := vk.mem.trans um
  refine ⟨?_, ⟨_, by rw [wm, hvm, hrc]⟩, by rw [wrd, vk.rd, urd], by rw [wwr, vk.wr, uwr],
    by rw [wsy, vsy, usy], ⟨fun r hr => ?_, by rw [wrd, vk.rd, urd], by rw [wwr, vk.wr, uwr]⟩⟩
  · have hum : u.mem = s.mem := um
    have hl (k : Nat) (hk : k < 4) :
        ent u.mem (u.syms s5678Sym) (gIdx s.mem (s.gpr .rcx) l.main.1 l.main.2.1 l.main.2.2.1
          l.main.2.2.2 k).toNat k =
        tableEnt Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5
          (gIdx s.mem (s.gpr .rcx) l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2 k).toNat k :=
      ent_table (by rw [hum, usy]; exact hheld) (gIdx_lt _ _ _ _ _ _ hk) hk
    rw [wax, hvm, hrc, hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hx]
    simp only [tableEnt, gIdx, ofNat_setWidth8, hm.pos ha, hm.pos hb, hm.pos hc, hm.pos hd]
    rcases hwd' : l.word with _ | ⟨a', q'⟩
    · simp only [withWord, lineVal, hwd']
    · simp only [withWord, lineVal, hwd', hm.quad a' (hq a' q' hwd')]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [wk.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1⟩),
      g r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1, hr.2.2.1⟩)
      hr.2.2.1 hr.2.2.2]

end VG.Proof.Cast5.X86_64

end

end

/-! ### `Cast5.X86_64.KeyHalf`, which only this module used -/

section

/-! ### `Cast5.X86_64.KeyGroup`, which only this module used -/

section

/-! ### `Cast5.X86_64.KeyMem`, which only this module used -/

section

/-!
# CAST5 key expansion on x86-64: the working space and the subkeys

The working space at `c` holds `x` and `z` (`HoldsXZ`) and the group's extra
lookups (`Extras`); the subkeys so far are at `K` (`Keys`). Each write of key
expansion keeps what it does not overwrite.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.Impl.Cast5 VG.Impl.Cast5.X86_64

/-- The group's extra lookups, lanes `0 … 3` at `c + 48`. -/
def Extras (m : Mem) (c : Addr) (f : Nat → Spec.Cast5.Word) : Prop :=
  ∀ j < 4, m.readW (c + BitVec.ofNat 64 (extraOff + 4 * j)) 32 = f j

/-- `Extras` after a write of `w / 8` bytes at `c + d`, below them. -/
theorem Extras.write {m : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {d w : Nat}
    (v : BitVec w) (hd : d + w / 8 ≤ extraOff) :
    Extras (m.writeW (c + BitVec.ofNat 64 d) v) c f := fun j hj => by
  rw [Mem.readW_writeW_sep (Offset.sep c (by unfold extraOff at *; omega_using [hd]) (by unfold extraOff; omega_using [hj])
    (by unfold extraOff at *; omega_using [hd])) (by decide)]
  exact h j hj

/-- `Extras` after a write elsewhere. -/
theorem Extras.write_disj {m : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {a : Addr}
    {w : Nat} (v : BitVec w) (hd : Region.Disjoint ⟨c, 64⟩ ⟨a, w / 8⟩) :
    Extras (m.writeW a v) c f := fun j hj => by
  rw [Mem.readW_writeW_sep (hd.sep (Offset.contains_base c (by unfold extraOff; omega_using [hj])
    (by unfold extraOff; omega_using [hj])) (Region.contains_self _ _)) (by decide)]
  exact h j hj

end VG.Proof.Cast5.X86_64

end

end


/-!
# CAST5 key expansion on x86-64: groups of four lines

A group (`lines4`) makes its four extra lookups (`extras_ok`), then runs its
lines, each storing its value into `x` or `z` (`groupQ_ok`) or as the next
subkey (`groupK_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

/-- The state of key expansion from the memory `m0`: the working space `c` in
`rcx`, writable, as is the schedule `K`; the table; and the memory (`KMem`). -/
structure KS (m0 : Mem) (c K : Addr) (s : State) (st : XZ) (ws : List Spec.Cast5.Word) : Prop where
  rc : s.gpr .rcx = c
  mem : KMem m0 s.mem c K st ws
  len : ws.length ≤ 32
  wS : InRegions s.wr c 64
  wK : InRegions s.wr K 128
  dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩
  tab : Readable s (s.syms s5678Sym)
  held : Held m0 (s.syms s5678Sym) s5678
  dT : ∀ r ∈ ([⟨c, 64⟩, ⟨K, 128⟩] : List Region), Region.Disjoint ⟨s.syms s5678Sym, 4096⟩ r

theorem KS.heldNow {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) : Held s.mem (s.syms s5678Sym) s5678 := by
  intro i hi
  have hl : s5678.length = 512 := table_length _ _ _ _
  rw [hl] at hi
  rw [h.mem.fr.readW (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) h.dT (by decide)]
  exact h.held i (by rw [hl]; exact hi)

/-- The same state, later: other registers, memory and flags. -/
theorem KS.update {m0 : Mem} {c K : Addr} {s u : State} {st st' : XZ} {ws ws' : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) (hc : u.gpr .rcx = s.gpr .rcx) (hm : KMem m0 u.mem c K st' ws')
    (hl : ws'.length ≤ 32) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) (hsy : u.syms = s.syms) :
    KS m0 c K u st' ws' where
  rc := hc.trans h.rc
  mem := hm
  len := hl
  wS := by rw [hwr]; exact h.wS
  wK := by rw [hwr]; exact h.wK
  dKS := h.dKS
  tab := by unfold Readable; rw [hsy, hrd, hwr]; exact h.tab
  held := by rw [hsy]; exact h.held
  dT := by rw [hsy]; exact h.dT

/-- A store of `xmm1` to the working space. -/
theorem store16_ok (v : State) (d : Nat) (h : InRegions v.wr (v.gpr .rcx + BitVec.ofNat 64 d) 16) :
    WP isa (.block [.movdquStore (at_ .rcx d) .xmm1]) v fun w =>
      w.mem = v.mem.writeW (v.gpr .rcx + BitVec.ofNat 64 d) (v.xmm .xmm1) ∧ w.gpr = v.gpr ∧
        w.rd = v.rd ∧ w.wr = v.wr ∧ w.syms = v.syms := by
  xrun [VG.Proof.Cast5.X86_64.ea_at, State.store128, h]

theorem extras_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {a b c' d : Pos} (ha : a.2 < 16) (hb : b.2 < 16) (hc : c'.2 < 16)
    (hd : d.2 < 16) :
    WP isa (extras a b c' d) s fun u => KS m0 c K u st ws ∧ Extras u.mem c (exVal st a b c' d) ∧
      u.syms = s.syms ∧ Keep [.rax, .r9, .r10, .r11] s u := by
  have hw : InRegions s.wr (s.gpr .rcx) 64 := by rw [h.rc]; exact h.wS
  have hin (q : Pos) (hq : q.2 < 16) : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (srcOff q)) 1 :=
    scr_rw hw (by obtain ⟨a', i'⟩ := q; have := off_lt a'; simp only [srcOff] at hq ⊢; omega_using [hq, this])
  unfold extras
  refine WP.seq (WP.mono_syms (WP.keep [.rax, .r9, .r10] (gather_ok s (hin _ ha) (hin _ hb) (hin _ hc)
    (hin _ hd)) (by rfl)) fun u ⟨⟨u0, um, urd, uwr⟩, uk⟩ usy => ?_)
  have hT' : Readable u (u.syms s5678Sym) := by unfold Readable; rw [usy, urd, uwr]; exact h.tab
  refine WP.seq (WP.mono_syms (scan_ok u s5678Sym u0 (fun k hk => gIdx_lt _ _ _ _ _ _ hk) hT')
    fun v ⟨v1, vk⟩ vsy => ?_)
  have g (r : Reg) (hr : r ∉ [Reg.rax, .r9, .r10]) (h10 : r ≠ .r10) (h11 : r ≠ .r11) : v.gpr r = s.gpr r :=
    (vk.gpr r h10 h11).trans (uk.1 r hr)
  have hrc : v.gpr .rcx = s.gpr .rcx := g .rcx (by decide) (by decide) (by decide)
  have h48 : InRegions v.wr (v.gpr .rcx + BitVec.ofNat 64 extraOff) 16 := by
    rw [vk.wr, uwr, hrc]; exact scr_w hw (by decide)
  have hvm : v.mem = s.mem := vk.mem.trans um
  refine WP.mono (store16_ok v extraOff h48) fun w ⟨wm, wg, wrd, wwr, wsy⟩ => ?_
  rw [v1, hvm, hrc, h.rc] at wm
  refine ⟨h.update (by rw [wg, hrc]) ?_ h.len (by rw [wrd, vk.rd, urd])
    (by rw [wwr, vk.wr, uwr]) (by rw [wsy, vsy, usy]), fun j hj => ?_, by rw [wsy, vsy, usy],
    ⟨fun r hr => ?_, by rw [wrd, vk.rd, urd], by rw [wwr, vk.wr, uwr]⟩⟩
  · rw [wm]
    exact h.mem.write h.dKS h.len _ (by decide) (.inr (by decide))
  · have hum : u.mem = s.mem := um
    have hl (k : Nat) (hk : k < 4) :
        ent u.mem (u.syms s5678Sym) (gIdx s.mem c a b c' d k).toNat k =
        tableEnt Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5 (gIdx s.mem c a b c' d k).toNat k :=
      ent_table (by rw [hum, usy]; exact h.heldNow) (gIdx_lt _ _ _ _ _ _ hk) hk
    rw [wm, ← Proof.Cast5.add_ofNat_add, rd_lane _ _ _ hj, dword_L _ hj, hl j hj]
    rcases cases4 hj with rfl | rfl | rfl | rfl <;>
      simp only [tableEnt, gIdx, exVal, ofNat_setWidth8, h.mem.xz.pos ha, h.mem.xz.pos hb, h.mem.xz.pos hc,
        h.mem.xz.pos hd]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [wg, g r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1,
      hr.2.2.1⟩) hr.2.2.1 hr.2.2.2]

theorem storeQuad_ok (u : State) (a : Arr) (q : Nat) {v : Spec.Cast5.Word} (hax : u.gpr .rax = v.setWidth 64)
    (hw : InRegions u.wr (u.gpr .rcx + BitVec.ofNat 64 (off a + 4 * q)) 4) :
    WP isa (.block (storeQuad a q)) u fun w =>
      w.mem = u.mem.writeW (u.gpr .rcx + BitVec.ofNat 64 (off a + 4 * q)) (byteRev32 v) ∧
      (∀ r, r ≠ .rax → w.gpr r = u.gpr r) ∧ w.rd = u.rd ∧ w.wr = u.wr ∧ w.syms = u.syms := by
  unfold storeQuad
  xrun [VG.Proof.Cast5.X86_64.ea_at, hax, hw, bswap32_eq]
  exact ⟨fun r hr => ite_eq_right hr, rfl⟩

theorem storeKey_ok (u : State) (k : Nat) {v : Spec.Cast5.Word} (hax : u.gpr .rax = v.setWidth 64)
    (hw : InRegions u.wr (u.gpr .rdx + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (storeKey k)) u fun w =>
      w.mem = u.mem.writeW (u.gpr .rdx + BitVec.ofNat 64 (4 * k)) v ∧ w.gpr = u.gpr ∧ w.rd = u.rd ∧
        w.wr = u.wr ∧ w.syms = u.syms := by
  unfold storeKey
  xrun [VG.Proof.Cast5.X86_64.ea_at, hax, hw]

theorem lineOk_extra {l : Impl.Cast5.Line} (hl : lineOk l = true) : 5 ≤ l.extra.1 ∧ l.extra.1 ≤ 8 := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  exact ⟨hl.1.1.2, hl.1.2⟩

/-- The line, from a state of key expansion. -/
theorem lineS_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {f : Nat → Spec.Cast5.Word} (hE : Extras s.mem c f) {l : Impl.Cast5.Line}
    (hl : lineOk l = true) (hx : f (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2)) :
    WP isa (line l) s fun u => u.gpr .rax = (lineVal st l).setWidth 64 ∧ KS m0 c K u st ws ∧
      Extras u.mem c f ∧ u.syms = s.syms ∧ Keep [.rax, .r9, .r10, .r11] s u := by
  have he := lineOk_extra hl
  have hw : InRegions s.wr (s.gpr .rcx) 64 := by rw [h.rc]; exact h.wS
  have hm : HoldsXZ s.mem (s.gpr .rcx) st := by rw [h.rc]; exact h.mem.xz
  have hx' : s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 (extraOff + 4 * (8 - l.extra.1))) 32 =
      sbox l.extra.1 (st.get l.extra.2) := by rw [h.rc, hE _ (by omega_using [he]), hx]
  refine WP.mono (line_ok s st l hl hw hm h.tab h.heldNow hx') fun u ⟨uax, ⟨w, um⟩, urd, uwr, usy, uk⟩ => ?_
  rw [h.rc] at um
  have hm0 := h.mem.write h.dKS h.len (d := 0) w (by decide) (.inl (by decide))
  have hE0 := hE.write (d := 0) w (by decide)
  rw [BitVec.add_zero] at hm0 hE0
  rw [← um] at hm0 hE0
  exact ⟨uax, h.update (uk.1 _ (by decide)) hm0 h.len urd uwr usy, hE0, usy, uk⟩

/-- A line storing into quadruple `q` of `a`. -/
theorem lineQ_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {f : Nat → Spec.Cast5.Word} (hE : Extras s.mem c f) {l : Impl.Cast5.Line}
    (hl : lineOk l = true) (hx : f (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2)) (a : Arr) {q : Nat}
    (hq : q < 4) :
    WP isa (line l) s fun u => WP isa (.block (storeQuad a q)) u fun v =>
      KS m0 c K v (st.put a q (lineVal st l)) ws ∧ Extras v.mem c f ∧ v.syms = s.syms ∧
        Keep [.rax, .r9, .r10, .r11] s v := by
  refine WP.mono (lineS_ok h hE hl hx) fun u ⟨uax, hu, uE, usy, uk⟩ => ?_
  have := off_lt a
  have hw : InRegions u.wr (u.gpr .rcx + BitVec.ofNat 64 (off a + 4 * q)) 4 := by
    rw [hu.rc]; exact scr_w hu.wS (by omega_using [hq, this])
  refine WP.mono (storeQuad_ok u a q uax hw) fun v ⟨vm, vg, vrd, vwr, vsy⟩ => ?_
  rw [hu.rc] at vm
  refine ⟨hu.update (vg _ (by decide)) (by rw [vm]; exact hu.mem.quad hu.dKS hu.len a hq _) hu.len vrd vwr vsy,
    by rw [vm]; exact uE.write _ (by unfold extraOff; omega_using [hq, this]), by rw [vsy, usy],
    ⟨fun r hr => by rw [vg r (fun e => hr (e ▸ List.mem_cons_self)), uk.1 r hr], by rw [vrd, uk.2.1],
      by rw [vwr, uk.2.2]⟩⟩

/-- A line storing the next subkey, `k` of those from `rdx`. -/
theorem lineK_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {f : Nat → Spec.Cast5.Word} (hE : Extras s.mem c f) {l : Impl.Cast5.Line}
    (hl : lineOk l = true) (hx : f (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2)) {k b : Nat}
    (hdx : s.gpr .rdx = K + BitVec.ofNat 64 b) (hb : b + 4 * k = 4 * ws.length) (hlen : ws.length < 32) :
    WP isa (line l) s fun u => WP isa (.block (storeKey k)) u fun v =>
      KS m0 c K v st (ws ++ [lineVal st l]) ∧ Extras v.mem c f ∧ v.syms = s.syms ∧
        Keep [.rax, .r9, .r10, .r11] s v := by
  refine WP.mono (lineS_ok h hE hl hx) fun u ⟨uax, hu, uE, usy, uk⟩ => ?_
  have hadr : u.gpr .rdx + BitVec.ofNat 64 (4 * k) = K + BitVec.ofNat 64 (4 * ws.length) := by
    rw [uk.1 _ (by decide), hdx, Proof.Cast5.add_ofNat_add, hb]
  have hw : InRegions u.wr (u.gpr .rdx + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hadr]; exact CallLay.inRegions_sub hu.wK (by omega_using [hlen]) (by decide)
  refine WP.mono (storeKey_ok u k uax hw) fun v ⟨vm, vg, vrd, vwr, vsy⟩ => ?_
  rw [hadr] at vm
  have hd : Region.Disjoint ⟨c, 64⟩ ⟨K + BitVec.ofNat 64 (4 * ws.length), 32 / 8⟩ :=
    (hu.dKS.sub_left (Offset.sub_base K (by omega_using [hlen]))).symm
  refine ⟨hu.update (by rw [vg]) (by rw [vm]; exact hu.mem.key hu.dKS hlen _)
      (by rw [List.length_append, List.length_singleton]; omega_using [hlen]) vrd vwr vsy,
    by rw [vm]; exact uE.write_disj _ hd, by rw [vsy, usy],
    ⟨fun r hr => by rw [vg, uk.1 r hr], by rw [vrd, uk.2.1], by rw [vwr, uk.2.2]⟩⟩

theorem keep_same {rs : List Reg} {s t u : State} (h₁ : Keep rs s t) (h₂ : Keep rs t u) : Keep rs s u :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

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
theorem groupQ_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) (a : Arr) {ls : List Impl.Cast5.Line} (hg : GroupOk (some a) ls) :
    WP isa (lines4 ls (storeQuad a)) s fun u =>
      KS m0 c K u (runQ a ls 4 st) ws ∧ u.syms = s.syms ∧ Keep [.rax, .r9, .r10, .r11] s u := by
  refine WP.mono (lines4_ok (fun k u => KS m0 c K u (runQ a ls k st) ws ∧
      Extras u.mem c (exVal st (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ∧
      u.syms = s.syms ∧ Keep [.rax, .r9, .r10, .r11] s u)
    (extras_ok h (hg.2 0 (by decide)) (hg.2 1 (by decide)) (hg.2 2 (by decide)) (hg.2 3 (by decide)))
    fun k hk u ⟨hu, uE, usy, uk⟩ => ?_) fun u ⟨hu, _, usy, uk⟩ => ⟨hu, usy, uk⟩
  obtain ⟨hok, hex, hna⟩ := hg.1 k hk
  have he := lineOk_extra hok
  refine WP.mono (lineQ_ok hu uE hok ?_ a hk) fun v hv => WP.mono hv fun w ⟨hw, wE, wsy, wk⟩ => ?_
  · rw [exVal_sbox _ _ he.1 he.2, hex, get_runQ _ _ _ _ fun e => hna (by rw [e])]
  · rw [runQ_succ]
    exact ⟨hw, wE, by rw [wsy, usy], keep_same uk wk⟩

/-- A group of lines storing subkeys `b … b + 3` from `rdx`, `K + 64 h`. -/
theorem groupK_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {ls : List Impl.Cast5.Line} (hg : GroupOk none ls) {b hh : Nat}
    (hdx : s.gpr .rdx = K + BitVec.ofNat 64 (64 * hh)) (hlen : ws.length = 16 * hh + b)
    (hle : ws.length + 4 ≤ 32) :
    WP isa (lines4 ls fun k => storeKey (b + k)) s fun u =>
      KS m0 c K u st (ws ++ keys4 ls st) ∧ u.syms = s.syms ∧ Keep [.rax, .r9, .r10, .r11] s u := by
  refine WP.mono (lines4_ok (fun k u => KS m0 c K u st (ws ++ (keys4 ls st).take k) ∧
      Extras u.mem c (exVal st (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ∧
      u.syms = s.syms ∧ Keep [.rax, .r9, .r10, .r11] s u)
    (WP.mono (extras_ok h (hg.2 0 (by decide)) (hg.2 1 (by decide)) (hg.2 2 (by decide))
      (hg.2 3 (by decide))) fun u ⟨hu, uE, usy, uk⟩ => ⟨by rw [List.take_zero, List.append_nil]; exact hu,
        uE, usy, uk⟩)
    fun k hk u ⟨hu, uE, usy, uk⟩ => ?_) fun u ⟨hu, _, usy, uk⟩ => ⟨hu, usy, uk⟩
  obtain ⟨hok, hex, _⟩ := hg.1 k hk
  have he := lineOk_extra hok
  have hl : (ws ++ (keys4 ls st).take k).length = ws.length + k := by
    rw [List.length_append, List.length_take, show (keys4 ls st).length = 4 from rfl, Nat.min_eq_left (by omega_using [hk])]
  refine WP.mono (lineK_ok hu uE hok ?_ (k := b + k) (b := 64 * hh) (by rw [uk.1 _ (by decide), hdx])
      (by rw [hl, hlen]; omega_using []) (by rw [hl]; omega_using [hle, hk])) fun v hv => WP.mono hv fun w ⟨hw, wE, wsy, wk⟩ => ?_
  · rw [exVal_sbox _ _ he.1 he.2, hex]
  · rw [take_keys4 _ _ hk, ← List.append_assoc]
    exact ⟨hw, wE, by rw [wsy, usy], keep_same uk wk⟩

end VG.Proof.Cast5.X86_64

end

end


/-!
# CAST5 key expansion on x86-64: a half

`half` runs the eight groups of lines of §2.4 (`halfImpl`), writing sixteen
subkeys from `rdx`, then moves `rdx` on and counts the half (`half_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly sx_ofNat)

theorem gZ : GroupOk (some .z) zLines := by unfold GroupOk; decide
theorem gX : GroupOk (some .x) xLines := by unfold GroupOk; decide
theorem gA : GroupOk none aLines := by unfold GroupOk; decide
theorem gB : GroupOk none bLines := by unfold GroupOk; decide
theorem gC : GroupOk none cLines := by unfold GroupOk; decide
theorem gD : GroupOk none dLines := by unfold GroupOk; decide

theorem storeKey_zero : (fun k => storeKey (0 + k)) = storeKey := funext fun k => by rw [Nat.zero_add]

/-- The registers key expansion writes. -/
def keyRegs : List Reg := [.rax, .r9, .r10, .r11, .rdx, .rsi]

theorem half_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {hh : Nat} (hdx : s.gpr .rdx = K + BitVec.ofNat 64 (64 * hh))
    (hlen : ws.length = 16 * hh) (hle : hh < 2) :
    WP isa half s fun u =>
      KS m0 c K u (halfImpl st).2 (ws ++ (halfImpl st).1) ∧
      u.gpr .rdx = K + BitVec.ofNat 64 (64 * (hh + 1)) ∧ u.gpr .rsi = s.gpr .rsi - 1 ∧
      u.zf = some (s.gpr .rsi - 1 == 0) ∧ u.syms = s.syms ∧ Keep keyRegs s u := by
  have kd {u v : State} (k : Keep [.rax, .r9, .r10, .r11] u v) : v.gpr .rdx = u.gpr .rdx := k.1 _ (by decide)
  have l4 (ls : List Impl.Cast5.Line) (t : XZ) : (keys4 ls t).length = 4 := rfl
  unfold half
  refine WP.seq (WP.mono (groupQ_ok h .z gZ) fun u1 ⟨h1, s1, k1⟩ => ?_)
  rw [runQ_z] at h1
  have g2 := groupK_ok h1 gA (b := 0) (hh := hh) (by rw [kd k1, hdx]) (by rw [hlen]; rfl) (by omega_using [hlen, hle])
  rw [storeKey_zero] at g2
  refine WP.seq (WP.mono g2 fun u2 ⟨h2, s2, k2⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h2 .x gX) fun u3 ⟨h3, s3, k3⟩ => ?_)
  rw [runQ_x] at h3
  have g4 := groupK_ok h3 gB (b := 4) (hh := hh) (by rw [kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, hlen, l4]) (by rw [List.length_append, hlen, l4]; omega_using [hle])
  refine WP.seq (WP.mono g4 fun u4 ⟨h4, s4, k4⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h4 .z gZ) fun u5 ⟨h5, s5, k5⟩ => ?_)
  rw [runQ_z] at h5
  have g6 := groupK_ok h5 gC (b := 8) (hh := hh) (by rw [kd k5, kd k4, kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, List.length_append, hlen, l4, l4])
    (by rw [List.length_append, List.length_append, hlen, l4, l4]; omega_using [hle])
  refine WP.seq (WP.mono g6 fun u6 ⟨h6, s6, k6⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h6 .x gX) fun u7 ⟨h7, s7, k7⟩ => ?_)
  rw [runQ_x] at h7
  have g8 := groupK_ok h7 gD (b := 12) (hh := hh)
    (by rw [kd k7, kd k6, kd k5, kd k4, kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4]; omega_using [hle])
  refine WP.seq (WP.mono g8 fun u8 ⟨h8, s8, k8⟩ => ?_)
  have k18 := keep_same (keep_same (keep_same (keep_same (keep_same (keep_same (keep_same k1 k2) k3) k4) k5)
    k6) k7) k8
  have hdx8 : u8.gpr .rdx = K + BitVec.ofNat 64 (64 * hh) := by rw [k18.1 _ (by decide), hdx]
  have hsi8 : u8.gpr .rsi = s.gpr .rsi := k18.1 _ (by decide)
  xrun [imm, sx_ofNat (show 64 < 2 ^ 31 by decide), sx_ofNat (show 1 < 2 ^ 31 by decide), hdx8, hsi8]
  have e64 : K + BitVec.ofNat 64 (64 * hh) + 64#64 = K + BitVec.ofNat 64 (64 * (hh + 1)) := by
    rw [show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, Proof.Cast5.add_ofNat_add, Nat.mul_succ]
  have hst : (halfImpl st).2 = runX xLines (runZ zLines (runX xLines (runZ zLines st))) := rfl
  have hks : ws ++ (halfImpl st).1 = ws ++ keys4 aLines (runZ zLines st) ++
      keys4 bLines (runX xLines (runZ zLines st)) ++ keys4 cLines (runZ zLines (runX xLines (runZ zLines st))) ++
      keys4 dLines (runX xLines (runZ zLines (runX xLines (runZ zLines st)))) := by
    simp only [halfImpl, List.append_assoc]
  rw [hst, hks]
  refine ⟨h8.update (by simp only [gpr_setReg_of_ne _ _ (show Reg.rcx ≠ .rsi by decide), gpr_setFlags,
      gpr_setReg_of_ne _ _ (show Reg.rcx ≠ .rdx by decide)]) h8.mem h8.len rfl rfl rfl, e64,
    rfl, rfl, by
      show u8.syms = s.syms
      rw [s8, s7, s6, s5, s4, s3, s2, s1], fun r hr => ?_, k18.2.1, k18.2.2⟩
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_setReg_of_ne _ _ hr.2.2.2.2.2, gpr_setFlags, gpr_setReg_of_ne _ _ hr.2.2.2.2.1]
  exact k18.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1,
    hr.2.2.1, hr.2.2.2.1⟩)

end VG.Proof.Cast5.X86_64

end

end


/-!
# CAST5 key expansion on x86-64

`expandKey` pads the key with zeros into `x` (§2.5), then runs both halves of
§2.4 (`expandKey_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly sx_ofNat wp_countdown)

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_byte (m : Mem) (c : Addr) {d e : Nat} (hd : d + 8 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (BitVec.setWidth 64 (0#32))) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 8 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

theorem zero_ok (s : State) (key : Addr) (hw : InRegions s.wr (s.gpr .rcx) 64) :
    WP isa (.block [.mov32 .rax (imm 0), .store (at_ .rcx xOff) .rax, .store (at_ .rcx (xOff + 8)) .rax,
      .mov .rax (.reg .rcx), .alu .add .rax (imm xOff)]) s fun u =>
      CInv s.mem key (s.gpr .rcx) 0 u.mem ∧ u.gpr .rax = s.gpr .rcx + BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .rax → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms := by
  have h16 := scr_w hw (d := 16) (n := 8) (by decide)
  have h24 := scr_w hw (d := 24) (n := 8) (by decide)
  unfold xOff
  xrun [VG.Proof.Cast5.X86_64.ea_at, imm, sx_ofNat (show 16 < 2 ^ 31 by decide), h16, h24,
    Nat.reduceAdd]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, fun r hr => ?_, rfl⟩
  · rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, zero_byte _ _ (by decide) (by omega_using [hi]),
      zero_byte _ _ (by decide) (by omega_using [hi])]
    split <;> split <;> first | rfl | omega
  · rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, zero_byte _ _ (by decide) (by omega_using [hi]),
      zero_byte _ _ (by decide) (by omega_using [hi]), ite_eq_right (by omega_using []), ite_eq_right (by omega_using [])]
  · exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  · simp only [hr, ite_false]

theorem copyStep_ok (u : State) {m0 : Mem} {key c : Addr} {j : Nat} (hj : j < 16) (hI : CInv m0 key c j u.mem)
    (hdi : u.gpr .rdi = key + BitVec.ofNat 64 j) (hax : u.gpr .rax = c + BitVec.ofNat 64 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (key + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (c + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (key + BitVec.ofNat 64 j) = m0 (key + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 key c (j + 1) v.mem ∧ v.gpr .rdi = key + BitVec.ofNat 64 (j + 1) ∧
      v.gpr .rax = c + BitVec.ofNat 64 (16 + (j + 1)) ∧ v.gpr .rsi = u.gpr .rsi - 1 ∧
      v.zf = some (u.gpr .rsi - 1 == 0) ∧ (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .r9 → v.gpr r = u.gpr r) ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms := by
  unfold copyStep
  xrun [VG.Proof.Cast5.X86_64.ea_at, imm, sx_ofNat (show 1 < 2 ^ 31 by decide), hdi, hax, hr, hw, hk,
    Proof.Cast5.add_ofNat_add]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, by rw [Nat.add_assoc], rfl, rfl, fun r h1 h2 h3 h4 => ?_, rfl⟩
  · simp only [Mem.writeW]
    rw [byte_write _ _ _ (by omega_using [hj]) (by omega_using [hi])]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left ⟨Nat.le_refl _, by omega_using []⟩, ite_eq_left (by omega_using []), Nat.sub_self]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [hk]
    · rw [ite_eq_right (by omega_using [hij]), hI.x i hi]
      by_cases hl : i < j
      · rw [ite_eq_left hl, ite_eq_left (by omega_using [hl])]
      · rw [ite_eq_right hl, ite_eq_right (by omega_using [hij, hl])]
  · simp only [Mem.writeW]
    rw [byte_write _ _ _ (by omega_using [hj]) (by omega_using [hi]), ite_eq_right (by omega_using [hj])]
    exact hI.z i hi
  · exact hI.fr.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
  · simp only [h1, h2, h3, h4, ite_false]

/-- The facts of key expansion's precondition on this target (the shared
contract's, `Spec.Cast5.expandKeyContract`, with the table `VG_CAST5_S5678`). -/
structure KPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.syms s5678Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .rdx, 128⟩, ⟨s.gpr .rcx, 256⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s5678Sym + BitVec.ofNat 64 (8 * i)) 64 = s5678.getD i 0
  fitT : (s.syms s5678Sym).toNat + 4096 ≤ 2 ^ 64
  dTK : Region.Disjoint ⟨s.syms s5678Sym, 4096⟩ ⟨s.gpr .rdx, 128⟩
  dTS : Region.Disjoint ⟨s.syms s5678Sym, 4096⟩ ⟨s.gpr .rcx, 256⟩
  dkK : Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ⟨s.gpr .rdx, 128⟩
  dkS : Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ⟨s.gpr .rcx, 256⟩
  dKS : Region.Disjoint ⟨s.gpr .rdx, 128⟩ ⟨s.gpr .rcx, 256⟩
  dspk : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dspK : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 128⟩
  dspS : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 256⟩
  fk : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  fK : (s.gpr .rdx).toNat + 128 ≤ 2 ^ 64
  fS : (s.gpr .rcx).toNat + 256 ≤ 2 ^ 64
  len : 5 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 16

/-- The registers key expansion writes. -/
def keyAll : List Reg := [.rax, .r9, .r10, .r11, .rdx, .rsi, .rdi]

theorem expandKey_ok (s : State) (h : KPre s) :
    WP isa expandKey s fun u =>
      Spec.Cast5.scheduleAt u.mem (s.gpr .rdx) =
        Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) ∧
      Keep keyAll s u ∧ Frame [⟨s.gpr .rdx, 128⟩, ⟨s.gpr .rcx, 256⟩] s.mem u.mem := by
  obtain ⟨n, hn⟩ : ∃ n, (s.gpr .rsi).toNat = n := ⟨_, rfl⟩
  obtain ⟨key, hkey⟩ : ∃ key, s.gpr .rdi = key := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, s.gpr .rcx = c := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, s.gpr .rdx = K := ⟨_, rfl⟩
  have hl := h.len
  rw [hn] at hl
  have hwS : InRegions s.wr c 256 := by
    rw [h.wr, hc]; exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  have hwK : InRegions s.wr K 128 := by
    rw [h.wr, hK]; exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
  have hw64 : InRegions s.wr c 64 := by
    have := CallLay.inRegions_sub hwS (off := 0) (l := 64) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have hrK : InRegions (s.rd ++ s.wr) key n := by
    rw [h.rd, hkey, hn]; exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
  have dkc : Region.Disjoint ⟨key, n⟩ ⟨c, 64⟩ := by
    have := h.dkS; rw [hkey, hn, hc] at this; exact this.sub_right (Region.sub_prefix (by decide))
  unfold expandKey
  refine WP.seq (WP.mono (zero_ok s key (by rw [hc]; exact hw64)) fun u0 ⟨c0, ax0, g0, rd0, wr0, sy0⟩ => ?_)
  rw [hc] at c0 ax0
  have hkb (j : Nat) (hj : j < n) (m : Mem) (hf : Frame [⟨c, 64⟩] s.mem m) :
      m (key + BitVec.ofNat 64 j) = s.mem (key + BitVec.ofNat 64 j) := by
    refine hf.bytes (R := ⟨key, n⟩) (fun r hr => ?_) (by show n ≤ 2 ^ 64; omega_using [hn]) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact dkc
  have hsi0 : u0.gpr .rsi = BitVec.ofNat 64 n := by
    rw [g0 _ (by decide), ← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (wp_countdown (cnt := .rsi) (N := n) (by omega_using [hn]) (by omega_using [hl])
    (fun j u => CInv s.mem key c j u.mem ∧ u.gpr .rdi = key + BitVec.ofNat 64 j ∧
      u.gpr .rax = c + BitVec.ofNat 64 (16 + j) ∧ (∀ r, r ∉ [Reg.rax, .rdi, .rsi, .r9] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms)
    (fun j hj u ⟨cu, du, au, gu, rdu, wru, syu⟩ _ => WP.mono (copyStep_ok u (by omega_using [hl, hj]) cu du au
      (by rw [rdu, wru]; exact CallLay.inRegions_sub hrK (by omega_using [hj]) (by omega_using [hn]))
      (by rw [wru]; exact scr_w hw64 (by omega_using [hl, hj]))
      (hkb j hj u.mem cu.fr))
      fun v ⟨cv, dv, av, sv, zv, gv, rdv, wrv, syv⟩ => ⟨⟨cv, dv, av, fun r hr => ?keepStep, rdv.trans rdu,
        wrv.trans wru, syv.trans syu⟩, sv, zv⟩)
    (fun u hu => ?rest) ⟨c0, by rw [g0 _ (by decide), hkey, BitVec.add_zero], by rw [ax0], fun r hr => ?keep0, rd0,
      wr0, sy0⟩ hsi0)
  case keepStep =>
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [gv r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2, gu r hr]
  case keep0 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g0 r hr.1
  case rest =>
    obtain ⟨cu, -, -, gu, rdu, wru, syu⟩ := hu
    refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rsi (imm 2)]) u fun v =>
        v.gpr .rsi = BitVec.ofNat 64 2 ∧ v.mem = u.mem ∧ (∀ r, r ≠ .rsi → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
          v.wr = u.wr ∧ v.syms = u.syms by
      xrun [imm]
      exact ⟨fun r hr => ite_eq_right hr, rfl⟩) fun u1 ⟨si1, m1, g1, rd1, wr1, sy1⟩ => ?_)
    have g1s (r : Reg) (hr : r ∉ [Reg.rax, .rdi, .rsi, .r9]) : u1.gpr r = s.gpr r := by
      rw [g1 r (fun e => hr (by rw [e]; simp)), gu r hr]
    let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem key n).getD j 0,
      fun j => s.mem (c + BitVec.ofNat 64 (32 + j))⟩
    have hT : s.syms s5678Sym = u1.syms s5678Sym := by rw [sy1, syu]
    have xz0 : HoldsXZ u1.mem c st0 := by
      intro a i hi
      rw [m1]
      cases a with
      | x => rw [show off .x + i = 16 + i from rfl, cu.x i hi]; exact (bytesAt_getD _ _ _ _).symm
      | z => exact cu.z i hi
    have fr0 : Frame [⟨c, 64⟩, ⟨K, 128⟩] s.mem u1.mem := by
      rw [m1]
      refine cu.fr.mono fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hr]; exact List.mem_cons_self
    have tab0 : Readable u1 (u1.syms s5678Sym) := by
      unfold Readable; rw [rd1, rdu, wr1, wru, ← hT, h.rd]
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
    have held0 : Held s.mem (u1.syms s5678Sym) s5678 := by
      rw [← hT]; intro i hi
      rw [show s5678.length = 512 from table_length _ _ _ _] at hi
      exact h.held i hi
    have dT0 : ∀ r ∈ ([⟨c, 64⟩, ⟨K, 128⟩] : List Region), Region.Disjoint ⟨u1.syms s5678Sym, 4096⟩ r := by
      intro r hr
      rw [← hT]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have := h.dTS; rw [hc] at this; exact this.sub_right (Region.sub_prefix (by decide))
      · have := h.dTK; rw [hK] at this; exact this
    have dKS0 : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩ := by
      have := h.dKS; rw [hK, hc] at this; exact this.sub_right (Region.sub_prefix (by decide))
    have ks0 : KS s.mem c K u1 st0 [] :=
      ⟨by rw [g1s _ (by decide), hc], ⟨xz0, fun i hi => absurd hi (Nat.not_lt_zero _), fr0⟩, Nat.zero_le _,
        by rw [wr1, wru]; exact hw64, by rw [wr1, wru]; exact hwK, dKS0, tab0, held0, dT0⟩
    refine wp_countdown (cnt := .rsi) (N := 2) (by decide) (by decide)
      (fun hh v => KS s.mem c K v (halves st0 hh).1 (halves st0 hh).2 ∧
        v.gpr .rdx = K + BitVec.ofNat 64 (64 * hh) ∧ v.syms = s.syms ∧ Keep keyRegs u1 v)
      (fun hh hh2 v ⟨kv, dv, syv, kpv⟩ _ => WP.mono (half_ok kv dv (halves_length st0 hh) hh2)
        fun w ⟨kw, dw, sw, zw, syw, kpw⟩ => ⟨⟨kw, dw, syw.trans syv, keep_same kpv kpw⟩, sw, zw⟩)
      (fun v ⟨kv, _, _, kpv⟩ => ?_)
      ⟨ks0, by rw [g1s _ (by decide), hK, Nat.mul_zero, BitVec.add_zero], by rw [sy1, syu],
        Keep.refl _ _⟩ si1
    rw [hK, hkey, hn, hc]
    refine ⟨?_, ⟨fun r hr => ?_, by rw [kpv.2.1, rd1, rdu], by rw [kpv.2.2, wr1, wru]⟩, ?_⟩
    · rw [scheduleAt_keys kv.mem.keys (halves_length st0 2), Proof.Cast5.expandKey_eq _ st0.z, halves_two]
    · simp only [keyAll, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [kpv.1 r (by simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1⟩)]
      exact g1s r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨hr.1, hr.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.1⟩)
    · refine kv.mem.fr.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩

end VG.Proof.Cast5.X86_64
