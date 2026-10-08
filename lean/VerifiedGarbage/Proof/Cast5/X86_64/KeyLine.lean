import VerifiedGarbage.Proof.Cast5.X86_64.Block
import VerifiedGarbage.Proof.Cast5.KeyLines

/-!
# CAST5 key expansion on x86-64: a line

`line l` gathers the line's four main bytes from the working space into the
lanes of `xmm0` (`gather_ok`), scans `VG_CAST5_S5678`, and XORs the four
values, the group's extra lookup and the quadruple, if any (`line_ok`).
-/

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
  · rw [BitVec.getLsbD_of_ge x i (by omega)]; simp [h]

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

/-- `[p + e, p + e + k)` and `[p, p + n)` are separate if `n ≤ e`. -/
theorem sep_base' (p : Addr) {n e k : Nat} (h : n ≤ e) (he : e + k ≤ 2 ^ 64) :
    Mem.Sep (p + BitVec.ofNat 64 e) k p n :=
  fun x h₁ h₂ => Offset.sep_base p h he x h₂ h₁

theorem off_lt (a : Arr) : off a + 16 ≤ 48 := by cases a <;> decide
theorem off_ge (a : Arr) : 16 ≤ off a := by cases a <;> decide

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
  have ex := scr_rw hw (d := extraOff + 4 * (8 - e)) (n := 4) (by unfold extraOff; omega)
  have w0 : InRegions s.wr (s.gpr .rcx) 16 := by
    have := scr_w hw (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this
  have d0 : dword (L v) 0 = v 0 := dword_L v (by decide)
  have d1 : dword (L v) 1 = v 1 := dword_L v (by decide)
  have d2 : dword (L v) 2 = v 2 := dword_L v (by decide)
  have d3 : dword (L v) 3 = v 3 := dword_L v (by decide)
  have sx : (s.mem.writeW (s.gpr .rcx) (L v)).readW
      (s.gpr .rcx + BitVec.ofNat 64 (extraOff + 4 * (8 - e))) 32 =
      s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 (extraOff + 4 * (8 - e))) 32 :=
    Mem.readW_writeW_sep (sep_base' _ (by unfold extraOff; omega) (by unfold extraOff; omega))
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
    have eq := scr_rw hw (d := off a + 4 * q) (n := 4) (by have := off_lt a; omega)
    have sq : (s.mem.writeW (s.gpr .rcx) (L v)).readW (s.gpr .rcx + BitVec.ofNat 64 (off a + 4 * q)) 32 =
        s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 (off a + 4 * q)) 32 :=
      Mem.readW_writeW_sep (sep_base' _ (by have := off_ge a; omega)
        (by have := off_lt a; omega)) (by decide)
    xrun [VG.Proof.Cast5.X86_64.ea_at, State.store128, w0, h1, e0, e1, e2, e3, ex, eq, rd_lane0, rd_lane1,
      rd_lane2, rd_lane3, d0, d1, d2, d3, sx, sq, List.cons_append, List.nil_append, bswap32_eq]
    exact ⟨rfl, rfl⟩

theorem tail_writes (e : Nat) (wd : Option (Arr × Nat)) :
    writesOnly [.rax, .r9] (.block (tail e wd)) = true := by
  cases wd with
  | none => rfl
  | some aq => obtain ⟨a, q⟩ := aq; rfl

/-- The working space at `p` holds the arrays of `st`, a byte each. -/
def HoldsXZ (m : Mem) (p : Addr) (st : XZ) : Prop :=
  ∀ a i, i < 16 → m (p + BitVec.ofNat 64 (off a + i)) = st.arr a i

theorem HoldsXZ.pos {m : Mem} {p : Addr} {st : XZ} (h : HoldsXZ m p st) {q : Pos} (hq : q.2 < 16) :
    m (p + BitVec.ofNat 64 (srcOff q)) = st.get q := by
  obtain ⟨a, i⟩ := q
  cases a <;> exact h _ i hq

theorem HoldsXZ.quad {m : Mem} {p : Addr} {st : XZ} (h : HoldsXZ m p st) (a : Arr) {q : Nat} (hq : q < 4) :
    byteRev32 (m.readW (p + BitVec.ofNat 64 (off a + 4 * q)) 32) = quadOf (st.arr a) q := by
  have e1 : (1 : Addr) = BitVec.ofNat 64 1 := rfl
  rw [byteRev32_readW, e1, Proof.Cast5.add_ofNat_add, Proof.Cast5.add_ofNat_add,
    Proof.Cast5.add_ofNat_add, quadOf, show off a + 4 * q + 1 + 1 + 1 = off a + (4 * q + 3) by omega,
    show off a + 4 * q + 1 + 1 = off a + (4 * q + 2) by omega,
    show off a + 4 * q + 1 = off a + (4 * q + 1) by omega, h a _ (by omega), h a _ (by omega),
    h a _ (by omega), h a _ (by omega)]

/-- What `line_ok` needs of a line: its bytes are in `x` and `z`, its extra
S-box one of S5–S8, its quadruple one of four. -/
def lineOk (l : Impl.Cast5.Line) : Bool :=
  l.main.1.2 < 16 && l.main.2.1.2 < 16 && l.main.2.2.1.2 < 16 && l.main.2.2.2.2 < 16 &&
    5 ≤ l.extra.1 && l.extra.1 ≤ 8 &&
    (match l.word with | some (_, q) => q < 4 | none => true)

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
    scr_rw hw (by obtain ⟨a', i'⟩ := q; have := off_lt a'; simp only [srcOff] at hq ⊢; omega)
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
