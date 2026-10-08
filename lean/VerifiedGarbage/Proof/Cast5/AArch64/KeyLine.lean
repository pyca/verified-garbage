import VerifiedGarbage.Proof.Cast5.AArch64.Block
import VerifiedGarbage.Proof.Cast5.KeyMem

/-!
# CAST5 key expansion on AArch64: a line

`line l` gathers the line's four main bytes from the working space into the
lanes of `v0` (`gather_ok`), scans `VG_CAST5_S5678`, and XORs the four
values, the group's extra lookup (a lane of `v6`) and the quadruple, if any
(`line_ok`). It writes no memory.
-/

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The index lanes of a gather: the bytes at `d`, `c`, `b`, `a`. -/
def gIdx (m : Mem) (p : Addr) (a b c d : Pos) : Nat → BitVec 32
  | 0 => (m (p + BitVec.ofNat 64 (srcOff d))).setWidth 32
  | 1 => (m (p + BitVec.ofNat 64 (srcOff c))).setWidth 32
  | 2 => (m (p + BitVec.ofNat 64 (srcOff b))).setWidth 32
  | _ => (m (p + BitVec.ofNat 64 (srcOff a))).setWidth 32

theorem setWidth_8_32_64_32 (x : BitVec 8) : ((x.setWidth 32).setWidth 64).setWidth 32 = x.setWidth 32 :=
  setWidth_32_64_32 _

theorem srcOff_lt {q : Pos} (hq : q.2 < 16) : srcOff q < 4096 := by
  obtain ⟨a, i⟩ := q
  have := off_lt a
  simp only [srcOff] at hq ⊢
  omega

theorem gather_ok (s : State) {a b c d : Pos} (ha : a.2 < 16) (hb : b.2 < 16) (hc : c.2 < 16)
    (hd : d.2 < 16)
    (ra : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (srcOff a)) 1)
    (rb : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (srcOff b)) 1)
    (rc : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (srcOff c)) 1)
    (rd : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (srcOff d)) 1) :
    WP isa (.block (gather a b c d)) s fun u =>
      u.v .v0 = L (gIdx s.mem (s.gpr .x3) a b c d) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
        (∀ x, x ≠ .v0 → u.v x = s.v x) := by
  have oa := srcOff_lt ha
  have ob := srcOff_lt hb
  have oc := srcOff_lt hc
  have od := srcOff_lt hd
  unfold gather
  crun [oa, ob, oc, od, ra, rb, rc, rd, setWidth_8_32_64_32]
  refine ⟨?_, fun x h0 => ?_⟩
  · rw [setLane_four]
    rfl
  · simp only [v_write, v_setV_of_ne _ _ h0]

/-- The value a line's last block computes from `v` and the memory `m`
holding its quadruple. -/
def withWord (m : Mem) (p : Addr) (v : Spec.Cast5.Word) : Option (Arr × Nat) → Spec.Cast5.Word
  | some (a, q) => v ^^^ byteRev32 (m.readW (p + BitVec.ofNat 64 (off a + 4 * q)) 32)
  | none => v

/-- The XORs of a line, after the scan. -/
def tail (e : Nat) (wd : Option (Arr × Nat)) : List Instr :=
  ([.umov .w .x0 .v1 0, .umov .w .x9 .v1 1, .logic .eor .w .x0 .x0 .x9, .umov .w .x9 .v1 2,
      .logic .eor .w .x0 .x0 .x9, .umov .w .x9 .v1 3, .logic .eor .w .x0 .x0 .x9,
      .umov .w .x9 .v6 (8 - e), .logic .eor .w .x0 .x0 .x9] : List Instr) ++
  (match wd with
    | some (a, q) => [.ldr .w .x9 .x3 (off a + 4 * q), .rev32 .x9 .x9, .logic .eor .w .x0 .x0 .x9]
    | none => [])

theorem line_eq (l : Impl.Cast5.Line) :
    line l = .seq (.block (gather l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2))
      (.seq (scan s5678Sym) (.block (tail l.extra.1 l.word))) := rfl

theorem tail_ok (s : State) {e : Nat} (he : 5 ≤ e) {wd : Option (Arr × Nat)}
    (hq : ∀ a q, wd = some (a, q) → q < 4) {v : Nat → Spec.Cast5.Word} (h1 : s.v .v1 = L v)
    (hw : InRegions (s.rd ++ s.wr) (s.gpr .x3) 64) :
    WP isa (.block (tail e wd)) s fun u =>
      u.gpr .x0 = (withWord s.mem (s.gpr .x3)
        (v 0 ^^^ v 1 ^^^ v 2 ^^^ v 3 ^^^ vword (s.v .v6) (8 - e)) wd).setWidth 64 ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧ u.v = s.v := by
  have d0 : vword (L v) 0 = v 0 := vword_L v (by decide)
  have d1 : vword (L v) 1 = v 1 := vword_L v (by decide)
  have d2 : vword (L v) 2 = v 2 := vword_L v (by decide)
  have d3 : vword (L v) 3 = v 3 := vword_L v (by decide)
  have he4 : 8 - e < 4 := by omega
  unfold tail
  cases wd with
  | none =>
    crun [h1, d0, d1, d2, d3, he4, List.append_nil]
    rfl
  | some aq =>
    obtain ⟨a, q⟩ := aq
    have hq4 := hq a q rfl
    have := off_lt a
    have ho : (off a + 4 * q) % 4 = 0 ∧ off a + 4 * q < 16384 := by
      cases a <;> simp only [off, xOff, zOff] <;> omega
    have eq : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (off a + 4 * q)) 4 :=
      CallLay.inRegions_sub hw (by omega) (by decide)
    crun [h1, d0, d1, d2, d3, he4, ho, eq, rev32_eq]
    rfl

theorem tail_writes (e : Nat) (wd : Option (Arr × Nat)) :
    writesOnly [.x0, .x9] (.block (tail e wd)) = true := by
  cases wd with
  | none => rfl
  | some aq => obtain ⟨a, q⟩ := aq; rfl

theorem tail_keepsV (e : Nat) (wd : Option (Arr × Nat)) :
    (Code.block (tail e wd) : Prog isa).allInstrs keepsV = true := by
  cases wd with
  | none => rfl
  | some aq => obtain ⟨a, q⟩ := aq; rfl

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

theorem pv_ne : ∀ r ∈ preservedV, r ≠ .v1 ∧ r ≠ .v2 ∧ r ≠ .v3 ∧ r ≠ .v4 ∧ r ≠ .v5 := by decide

/-- A line: `w0` := its value; no memory written. -/
theorem line_ok (s : State) (st : XZ) (l : Impl.Cast5.Line) (hl : lineOk l = true)
    (hw : InRegions (s.rd ++ s.wr) (s.gpr .x3) 64) (hm : HoldsXZ s.mem (s.gpr .x3) st)
    (hT : Readable s (s.syms s5678Sym)) (hheld : Held s.mem (s.syms s5678Sym) s5678)
    (hx : vword (s.v .v6) (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2)) :
    WP isa (line l) s fun u => u.gpr .x0 = (lineVal st l).setWidth 64 ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
      u.wr = s.wr ∧ u.syms = s.syms ∧ u.v .v6 = s.v .v6 ∧ Keep [.x0, .x9, .x10, .x11] s u := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he5⟩, _⟩, hwd⟩ := hl
  have hin (q : Pos) (hq : q.2 < 16) : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (srcOff q)) 1 :=
    CallLay.inRegions_sub hw (by obtain ⟨a', i'⟩ := q; have := off_lt a'; simp only [srcOff] at hq ⊢; omega)
      (by decide)
  rw [line_eq]
  refine WP.seq (WP.mono_syms (WP.keep [.x9] (gather_ok s ha hb hc hd (hin _ ha) (hin _ hb) (hin _ hc)
    (hin _ hd)) rfl rfl rfl) fun u ⟨⟨u0, um, urd, uwr, uv⟩, uk⟩ usy => ?_)
  have hT' : Readable u (u.syms s5678Sym) := by unfold Readable; rw [usy, urd, uwr]; exact hT
  refine WP.seq (WP.mono_syms (scan_ok u s5678Sym u0 (fun k hk => gIdx_lt _ _ _ _ _ _ hk) hT')
    fun v ⟨v1, vk⟩ vsy => ?_)
  have g (r : Reg) (hr : r ∉ [Reg.x9]) (h10 : r ≠ .x10) (h11 : r ≠ .x11) : v.gpr r = s.gpr r :=
    (vk.gpr r h10 h11).trans (uk.gpr r hr)
  have hrc : v.gpr .x3 = s.gpr .x3 := g .x3 (by decide) (by decide) (by decide)
  have hvw : InRegions (v.rd ++ v.wr) (v.gpr .x3) 64 := by rw [vk.rd, vk.wr, urd, uwr, hrc]; exact hw
  have hq : ∀ a q, l.word = some (a, q) → q < 4 := by
    intro a q h; rw [h] at hwd; simpa using hwd
  have hv6 : v.v .v6 = s.v .v6 :=
    (vk.v .v6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (uv .v6 (by decide))
  refine WP.mono (WP.keep [.x0, .x9] (tail_ok v he5 hq v1 hvw) (tail_writes _ _) rfl (tail_keepsV _ _))
    fun w ⟨⟨wx0, wm, wrd, wwr, wsy, wv⟩, wk⟩ => ?_
  have hvm : v.mem = s.mem := vk.mem.trans um
  refine ⟨?_, by rw [wm, hvm], by rw [wrd, vk.rd, urd], by rw [wwr, vk.wr, uwr], by rw [wsy, vsy, usy],
    by rw [wv, hv6], ⟨fun r hr => ?_, by rw [wk.rd, vk.rd, urd], by rw [wk.wr, vk.wr, uwr],
      by rw [wk.sp, vk.sp, uk.sp], fun r hr => by
        obtain ⟨n1, n2, n3, n4, n5⟩ := pv_ne r hr
        rw [wk.vcs r hr, vk.v r n1 n2 n3 n4 n5, uk.vcs r hr]⟩⟩
  · have hum : u.mem = s.mem := um
    have hl (k : Nat) (hk : k < 4) :
        ent u.mem (u.syms s5678Sym) (gIdx s.mem (s.gpr .x3) l.main.1 l.main.2.1 l.main.2.2.1
          l.main.2.2.2 k).toNat k =
        tableEnt Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5
          (gIdx s.mem (s.gpr .x3) l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2 k).toNat k :=
      ent_table (by rw [hum, usy]; exact hheld) (gIdx_lt _ _ _ _ _ _ hk) hk
    rw [wx0, hvm, hrc, hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hv6, hx]
    simp only [tableEnt, gIdx, ofNat_setWidth8, hm.pos ha, hm.pos hb, hm.pos hc, hm.pos hd]
    rcases hwd' : l.word with _ | ⟨a', q'⟩
    · simp only [withWord, lineVal, hwd']
    · simp only [withWord, lineVal, hwd', hm.quad a' (hq a' q' hwd')]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [wk.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1⟩),
      g r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr.2.1) hr.2.2.1 hr.2.2.2]

end VG.Proof.Cast5.AArch64
