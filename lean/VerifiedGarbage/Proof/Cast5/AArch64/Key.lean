module
public import VerifiedGarbage.Impl.Cast5.AArch64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Cast5.AArch64.Scan
public import VerifiedGarbage.Proof.Cast5.KeyMem
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Cast5.AArch64.Block
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Cast5.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! ### `Cast5.AArch64.KeyHalf`, which only this module used -/

section

/-! ### `Cast5.AArch64.KeyGroup`, which only this module used -/

section

/-! ### `Cast5.AArch64.KeyLine`, which only this module used -/

section

/-!
# CAST5 key expansion on AArch64: a line

`line l` gathers the line's four main bytes from the working space into the
lanes of `v0` (`gather_ok`), scans `VG_CAST5_S5678`, and XORs the four
values, the group's extra lookup (a lane of `v6`) and the quadruple, if any
(`line_ok`). It writes no memory.
-/

@[expose] public section

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
  omega_using [hq, this]

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
  have he4 : 8 - e < 4 := by omega_using [he]
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
      cases a <;> simp only [off, xOff, zOff] <;> omega_using [hq4]
    have eq : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (off a + 4 * q)) 4 :=
      CallLay.inRegions_sub hw (by omega_using [hq4, this]) (by decide)
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

theorem pv_ne : ∀ r ∈ preservedV, r ≠ .v1 ∧ r ≠ .v2 ∧ r ≠ .v3 ∧ r ≠ .v4 ∧ r ≠ .v5 ∧ r ≠ .v16 ∧ r ≠ .v17 ∧ r ≠ .v18 ∧ r ≠ .v19 := by decide

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
    CallLay.inRegions_sub hw (by obtain ⟨a', i'⟩ := q; have := off_lt a'; simp only [srcOff] at hq ⊢; omega_using [hq, this])
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
    (vk.v .v6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (uv .v6 (by decide))
  refine WP.mono (WP.keep [.x0, .x9] (tail_ok v he5 hq v1 hvw) (tail_writes _ _) rfl (tail_keepsV _ _))
    fun w ⟨⟨wx0, wm, wrd, wwr, wsy, wv⟩, wk⟩ => ?_
  have hvm : v.mem = s.mem := vk.mem.trans um
  refine ⟨?_, by rw [wm, hvm], by rw [wrd, vk.rd, urd], by rw [wwr, vk.wr, uwr], by rw [wsy, vsy, usy],
    by rw [wv, hv6], ⟨fun r hr => ?_, by rw [wk.rd, vk.rd, urd], by rw [wk.wr, vk.wr, uwr],
      by rw [wk.sp, vk.sp, uk.sp], fun r hr => by
        obtain ⟨n1, n2, n3, n4, n5, n16, n17, n18, n19⟩ := pv_ne r hr
        rw [wk.vcs r hr, vk.v r n1 n2 n3 n4 n5 n16 n17 n18 n19, uk.vcs r hr]⟩⟩
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

end

end


/-!
# CAST5 key expansion on AArch64: groups of four lines

A group (`lines4`) makes its four extra lookups into `v6` (`extras_ok`),
then runs its lines, each storing its value into `x` or `z` (`groupQ_ok`) or
as the next subkey (`groupK_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The state of key expansion from the memory `m0`: the working space `c` in
`x3`, writable, as is the schedule `K`; the table; and the memory (`KMem`). -/
structure KS (m0 : Mem) (c K : Addr) (s : State) (st : XZ) (ws : List Spec.Cast5.Word) : Prop where
  rc : s.gpr .x3 = c
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
  rw [h.mem.fr.readW (Offset.contains_base _ (by omega_arith) (by omega_arith)) h.dT (by decide)]
  exact h.held i (by rw [hl]; exact hi)

theorem KS.ws {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) : InRegions (s.rd ++ s.wr) (s.gpr .x3) 64 := by
  rw [h.rc]; obtain ⟨g, hg, hc⟩ := h.wS; exact ⟨g, List.mem_append_right _ hg, hc⟩

/-- The same state, later: other registers, memory and flags. -/
theorem KS.update {m0 : Mem} {c K : Addr} {s u : State} {st st' : XZ} {ws ws' : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) (hc : u.gpr .x3 = s.gpr .x3) (hm : KMem m0 u.mem c K st' ws')
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

theorem keep_same {rs : List Reg} {s t u : State} (h₁ : Keep rs s t) (h₂ : Keep rs t u) : Keep rs s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => (h₂.vcs r hr).trans (h₁.vcs r hr)⟩

theorem extras_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {a b c' d : Pos} (ha : a.2 < 16) (hb : b.2 < 16) (hc : c'.2 < 16)
    (hd : d.2 < 16) :
    WP isa (extras a b c' d) s fun u => KS m0 c K u st ws ∧ u.v .v6 = L (exVal st a b c' d) ∧
      u.syms = s.syms ∧ Keep [.x0, .x9, .x10, .x11] s u := by
  have hin (q : Pos) (hq : q.2 < 16) : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (srcOff q)) 1 :=
    CallLay.inRegions_sub h.ws (by obtain ⟨a', i'⟩ := q; have := off_lt a'; simp only [srcOff] at hq ⊢; omega_arith)
      (by decide)
  unfold extras
  refine WP.seq (WP.mono_syms (WP.keep [.x9] (gather_ok s ha hb hc hd (hin _ ha) (hin _ hb) (hin _ hc)
    (hin _ hd)) rfl rfl rfl) fun u ⟨⟨u0, um, urd, uwr, _⟩, uk⟩ usy => ?_)
  have hT' : Readable u (u.syms s5678Sym) := by unfold Readable; rw [usy, urd, uwr]; exact h.tab
  refine WP.seq (WP.mono_syms (scan_ok u s5678Sym u0 (fun k hk => gIdx_lt _ _ _ _ _ _ hk) hT')
    fun v ⟨v1, vk⟩ vsy => ?_)
  have g (r : Reg) (hr : r ∉ [Reg.x9]) (h10 : r ≠ .x10) (h11 : r ≠ .x11) : v.gpr r = s.gpr r :=
    (vk.gpr r h10 h11).trans (uk.gpr r hr)
  have hrc : v.gpr .x3 = s.gpr .x3 := g .x3 (by decide) (by decide) (by decide)
  have hvm : v.mem = s.mem := vk.mem.trans um
  refine WP.mono_syms (WP.keep [] (show WP isa (.block [.vop (.mov .v6 .v1)]) v fun w =>
      w.v .v6 = v.v .v1 ∧ w.mem = v.mem ∧ w.rd = v.rd ∧ w.wr = v.wr by crun) rfl rfl (by decide))
    fun w ⟨⟨w6, wm, wrd, wwr⟩, wk⟩ wsy => ?_
  refine ⟨h.update (by rw [wk.gpr _ (by decide), hrc]) (by rw [wm, hvm]; exact h.mem) h.len
    (by rw [wrd, vk.rd, urd]) (by rw [wwr, vk.wr, uwr]) (by rw [wsy, vsy, usy]), ?_, by rw [wsy, vsy, usy],
    ⟨fun r hr => ?_, by rw [wrd, vk.rd, urd], by rw [wwr, vk.wr, uwr], by rw [wk.sp, vk.sp, uk.sp],
      fun r hr => by
        obtain ⟨n1, n2, n3, n4, n5, n16, n17, n18, n19⟩ := pv_ne r hr
        rw [wk.vcs r hr, vk.v r n1 n2 n3 n4 n5 n16 n17 n18 n19, uk.vcs r hr]⟩⟩
  · have hum : u.mem = s.mem := um
    have hl (k : Nat) (hk : k < 4) :
        ent u.mem (u.syms s5678Sym) (gIdx s.mem (s.gpr .x3) a b c' d k).toNat k =
        tableEnt Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5
          (gIdx s.mem (s.gpr .x3) a b c' d k).toNat k :=
      ent_table (by rw [hum, usy]; exact h.heldNow) (gIdx_lt _ _ _ _ _ _ hk) hk
    have hm : HoldsXZ s.mem (s.gpr .x3) st := by rw [h.rc]; exact h.mem.xz
    rw [w6, v1]
    refine L_congr fun k hk => ?_
    rw [hl k hk]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_arith) with rfl | rfl | rfl | rfl <;>
      simp only [tableEnt, gIdx, exVal, ofNat_setWidth8, hm.pos ha, hm.pos hb, hm.pos hc, hm.pos hd]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [wk.gpr r (List.not_mem_nil), g r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr.2.1)
      hr.2.2.1 hr.2.2.2]

theorem storeQuad_ok (u : State) (a : Arr) {q : Nat} (hq : q < 4) {v : Spec.Cast5.Word}
    (hax : u.gpr .x0 = v.setWidth 64)
    (hw : InRegions u.wr (u.gpr .x3 + BitVec.ofNat 64 (off a + 4 * q)) 4) :
    WP isa (.block (storeQuad a q)) u fun w =>
      w.mem = u.mem.writeW (u.gpr .x3 + BitVec.ofNat 64 (off a + 4 * q)) (byteRev32 v) ∧
      (∀ r, r ≠ .x9 → w.gpr r = u.gpr r) ∧ w.rd = u.rd ∧ w.wr = u.wr ∧ w.v = u.v := by
  have ho : (off a + 4 * q) % 4 = 0 ∧ off a + 4 * q < 16384 := by
    cases a <;> simp only [off, xOff, zOff] <;> omega_arith
  unfold storeQuad
  crun [hax, hw, ho, rev32_eq]
  exact fun r hr => ite_eq_right hr

theorem storeKey_ok (u : State) {k : Nat} (hk : k < 32) {v : Spec.Cast5.Word}
    (hax : u.gpr .x0 = v.setWidth 64)
    (hw : InRegions u.wr (u.gpr .x2 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (storeKey k)) u fun w =>
      w.mem = u.mem.writeW (u.gpr .x2 + BitVec.ofNat 64 (4 * k)) v ∧ w.gpr = u.gpr ∧ w.rd = u.rd ∧
        w.wr = u.wr ∧ w.v = u.v := by
  have ho : (4 * k) % 4 = 0 ∧ 4 * k < 16384 := ⟨by omega_arith, by omega_arith⟩
  unfold storeKey
  crun [hax, hw, ho]

theorem lineOk_extra {l : Impl.Cast5.Line} (hl : lineOk l = true) : 5 ≤ l.extra.1 ∧ l.extra.1 ≤ 8 := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  exact ⟨hl.1.1.2, hl.1.2⟩

/-- The line, from a state of key expansion. -/
theorem lineS_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {f : Nat → Spec.Cast5.Word} (hE : s.v .v6 = L f) {l : Impl.Cast5.Line}
    (hl : lineOk l = true) (hx : f (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2)) :
    WP isa (line l) s fun u => u.gpr .x0 = (lineVal st l).setWidth 64 ∧ KS m0 c K u st ws ∧
      u.v .v6 = L f ∧ u.syms = s.syms ∧ Keep [.x0, .x9, .x10, .x11] s u := by
  have he := lineOk_extra hl
  have hm : HoldsXZ s.mem (s.gpr .x3) st := by rw [h.rc]; exact h.mem.xz
  have hx' : vword (s.v .v6) (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2) := by
    rw [hE, vword_L _ (by omega_arith), hx]
  refine WP.mono (line_ok s st l hl h.ws hm h.tab h.heldNow hx') fun u ⟨ux0, um, urd, uwr, usy, uv6, uk⟩ => ?_
  exact ⟨ux0, h.update (uk.gpr _ (by decide)) (by rw [um]; exact h.mem) h.len urd uwr usy, by rw [uv6, hE],
    usy, uk⟩

/-- A line storing into quadruple `q` of `a`. -/
theorem lineQ_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {f : Nat → Spec.Cast5.Word} (hE : s.v .v6 = L f) {l : Impl.Cast5.Line}
    (hl : lineOk l = true) (hx : f (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2)) (a : Arr) {q : Nat}
    (hq : q < 4) :
    WP isa (line l) s fun u => WP isa (.block (storeQuad a q)) u fun v =>
      KS m0 c K v (st.put a q (lineVal st l)) ws ∧ v.v .v6 = L f ∧ v.syms = s.syms ∧
        Keep [.x0, .x9, .x10, .x11] s v := by
  refine WP.mono (lineS_ok h hE hl hx) fun u ⟨ux0, hu, uE, usy, uk⟩ => ?_
  have := off_lt a
  have hw : InRegions u.wr (u.gpr .x3 + BitVec.ofNat 64 (off a + 4 * q)) 4 := by
    rw [hu.rc]; exact CallLay.inRegions_sub hu.wS (by omega_arith) (by decide)
  refine WP.mono_syms (WP.keep [.x9] (storeQuad_ok u a hq ux0 hw) rfl rfl rfl)
    fun v ⟨⟨vm, vg, vrd, vwr, vv⟩, vk⟩ vsy => ?_
  rw [hu.rc] at vm
  refine ⟨hu.update (vg _ (by decide)) (by rw [vm]; exact hu.mem.quad hu.dKS hu.len a hq _) hu.len vrd vwr vsy,
    by rw [vv, uE], by rw [vsy, usy], keep_same uk (vk.mono)⟩

/-- A line storing the next subkey, `k` of those from `x2`. -/
theorem lineK_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {f : Nat → Spec.Cast5.Word} (hE : s.v .v6 = L f) {l : Impl.Cast5.Line}
    (hl : lineOk l = true) (hx : f (8 - l.extra.1) = sbox l.extra.1 (st.get l.extra.2)) {k b : Nat}
    (hk : k < 32) (hdx : s.gpr .x2 = K + BitVec.ofNat 64 b) (hb : b + 4 * k = 4 * ws.length)
    (hlen : ws.length < 32) :
    WP isa (line l) s fun u => WP isa (.block (storeKey k)) u fun v =>
      KS m0 c K v st (ws ++ [lineVal st l]) ∧ v.v .v6 = L f ∧ v.syms = s.syms ∧
        Keep [.x0, .x9, .x10, .x11] s v := by
  refine WP.mono (lineS_ok h hE hl hx) fun u ⟨ux0, hu, uE, usy, uk⟩ => ?_
  have hadr : u.gpr .x2 + BitVec.ofNat 64 (4 * k) = K + BitVec.ofNat 64 (4 * ws.length) := by
    rw [uk.gpr _ (by decide), hdx, Proof.Cast5.add_ofNat_add, hb]
  have hw : InRegions u.wr (u.gpr .x2 + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hadr]; exact CallLay.inRegions_sub hu.wK (by omega_arith) (by decide)
  refine WP.mono_syms (WP.keep [] (storeKey_ok u hk ux0 hw) rfl rfl rfl)
    fun v ⟨⟨vm, vg, vrd, vwr, vv⟩, vk⟩ vsy => ?_
  rw [hadr] at vm
  refine ⟨hu.update (by rw [vg]) (by rw [vm]; exact hu.mem.key hu.dKS hlen _)
      (by rw [List.length_append, List.length_singleton]; omega_arith) vrd vwr vsy,
    by rw [vv, uE], by rw [vsy, usy], keep_same uk (vk.mono)⟩

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
      KS m0 c K u (runQ a ls 4 st) ws ∧ u.syms = s.syms ∧ Keep [.x0, .x9, .x10, .x11] s u := by
  refine WP.mono (lines4_ok (fun k u => KS m0 c K u (runQ a ls k st) ws ∧
      u.v .v6 = L (exVal st (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ∧
      u.syms = s.syms ∧ Keep [.x0, .x9, .x10, .x11] s u)
    (extras_ok h (hg.2 0 (by decide)) (hg.2 1 (by decide)) (hg.2 2 (by decide)) (hg.2 3 (by decide)))
    fun k hk u ⟨hu, uE, usy, uk⟩ => ?_) fun u ⟨hu, _, usy, uk⟩ => ⟨hu, usy, uk⟩
  obtain ⟨hok, hex, hna⟩ := hg.1 k hk
  have he := lineOk_extra hok
  refine WP.mono (lineQ_ok hu uE hok ?_ a hk) fun v hv => WP.mono hv fun w ⟨hw, wE, wsy, wk⟩ => ?_
  · rw [exVal_sbox _ _ he.1 he.2, hex, get_runQ _ _ _ _ fun e => hna (by rw [e])]
  · rw [runQ_succ]
    exact ⟨hw, wE, by rw [wsy, usy], keep_same uk wk⟩

/-- A group of lines storing subkeys `b … b + 3` from `x2`, `K + 64 h`. -/
theorem groupK_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {ls : List Impl.Cast5.Line} (hg : GroupOk none ls) {b hh : Nat}
    (hb : b + 4 ≤ 16) (hdx : s.gpr .x2 = K + BitVec.ofNat 64 (64 * hh)) (hlen : ws.length = 16 * hh + b)
    (hle : ws.length + 4 ≤ 32) :
    WP isa (lines4 ls fun k => storeKey (b + k)) s fun u =>
      KS m0 c K u st (ws ++ keys4 ls st) ∧ u.syms = s.syms ∧ Keep [.x0, .x9, .x10, .x11] s u := by
  refine WP.mono (lines4_ok (fun k u => KS m0 c K u st (ws ++ (keys4 ls st).take k) ∧
      u.v .v6 = L (exVal st (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ∧
      u.syms = s.syms ∧ Keep [.x0, .x9, .x10, .x11] s u)
    (WP.mono (extras_ok h (hg.2 0 (by decide)) (hg.2 1 (by decide)) (hg.2 2 (by decide))
      (hg.2 3 (by decide))) fun u ⟨hu, uE, usy, uk⟩ => ⟨by rw [List.take_zero, List.append_nil]; exact hu,
        uE, usy, uk⟩)
    fun k hk u ⟨hu, uE, usy, uk⟩ => ?_) fun u ⟨hu, _, usy, uk⟩ => ⟨hu, usy, uk⟩
  obtain ⟨hok, hex, _⟩ := hg.1 k hk
  have he := lineOk_extra hok
  have hl : (ws ++ (keys4 ls st).take k).length = ws.length + k := by
    rw [List.length_append, List.length_take, show (keys4 ls st).length = 4 from rfl, Nat.min_eq_left (by omega_arith)]
  refine WP.mono (lineK_ok hu uE hok ?_ (k := b + k) (b := 64 * hh) (by omega_arith) (by rw [uk.gpr _ (by decide), hdx])
      (by rw [hl, hlen]; omega_arith) (by rw [hl]; omega_arith)) fun v hv => WP.mono hv fun w ⟨hw, wE, wsy, wk⟩ => ?_
  · rw [exVal_sbox _ _ he.1 he.2, hex]
  · rw [take_keys4 _ _ hk, ← List.append_assoc]
    exact ⟨hw, wE, by rw [wsy, usy], keep_same uk wk⟩

end VG.Proof.Cast5.AArch64

end

end


/-!
# CAST5 key expansion on AArch64: a half

`half` runs the eight groups of lines of §2.4 (`halfImpl`), writing sixteen
subkeys from `x2`, then moves `x2` on and counts the half (`half_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem gZ : GroupOk (some .z) zLines := by unfold GroupOk; decide
theorem gX : GroupOk (some .x) xLines := by unfold GroupOk; decide
theorem gA : GroupOk none aLines := by unfold GroupOk; decide
theorem gB : GroupOk none bLines := by unfold GroupOk; decide
theorem gC : GroupOk none cLines := by unfold GroupOk; decide
theorem gD : GroupOk none dLines := by unfold GroupOk; decide

theorem storeKey_zero : (fun k => storeKey (0 + k)) = storeKey := funext fun k => by rw [Nat.zero_add]

/-- The registers key expansion's halves write. -/
def keyRegs : List Reg := [.x0, .x9, .x10, .x11, .x2, .x1]

theorem keep_widen {s u : State} (h : Keep [.x0, .x9, .x10, .x11] s u) : Keep keyRegs s u :=
  Keep.mono h

theorem half_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {hh : Nat} (hdx : s.gpr .x2 = K + BitVec.ofNat 64 (64 * hh))
    (hlen : ws.length = 16 * hh) (hle : hh < 2) :
    WP isa half s fun u =>
      KS m0 c K u (halfImpl st).2 (ws ++ (halfImpl st).1) ∧
      u.gpr .x2 = K + BitVec.ofNat 64 (64 * (hh + 1)) ∧ u.gpr .x1 = s.gpr .x1 - BitVec.ofNat 64 1 ∧
      u.syms = s.syms ∧ Keep keyRegs s u := by
  have kd {u v : State} (k : Keep [.x0, .x9, .x10, .x11] u v) : v.gpr .x2 = u.gpr .x2 := k.gpr _ (by decide)
  have l4 (ls : List Impl.Cast5.Line) (t : XZ) : (keys4 ls t).length = 4 := rfl
  unfold half
  refine WP.seq (WP.mono (groupQ_ok h .z gZ) fun u1 ⟨h1, s1, k1⟩ => ?_)
  rw [runQ_z] at h1
  have g2 := groupK_ok h1 gA (b := 0) (hh := hh) (by decide) (by rw [kd k1, hdx]) (by rw [hlen]; rfl)
    (by omega_using [hlen, hle])
  rw [storeKey_zero] at g2
  refine WP.seq (WP.mono g2 fun u2 ⟨h2, s2, k2⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h2 .x gX) fun u3 ⟨h3, s3, k3⟩ => ?_)
  rw [runQ_x] at h3
  have g4 := groupK_ok h3 gB (b := 4) (hh := hh) (by decide) (by rw [kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, hlen, l4]) (by rw [List.length_append, hlen, l4]; omega_using [hle])
  refine WP.seq (WP.mono g4 fun u4 ⟨h4, s4, k4⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h4 .z gZ) fun u5 ⟨h5, s5, k5⟩ => ?_)
  rw [runQ_z] at h5
  have g6 := groupK_ok h5 gC (b := 8) (hh := hh) (by decide) (by rw [kd k5, kd k4, kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, List.length_append, hlen, l4, l4])
    (by rw [List.length_append, List.length_append, hlen, l4, l4]; omega_using [hle])
  refine WP.seq (WP.mono g6 fun u6 ⟨h6, s6, k6⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h6 .x gX) fun u7 ⟨h7, s7, k7⟩ => ?_)
  rw [runQ_x] at h7
  have g8 := groupK_ok h7 gD (b := 12) (hh := hh) (by decide)
    (by rw [kd k7, kd k6, kd k5, kd k4, kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4]; omega_using [hle])
  refine WP.seq (WP.mono g8 fun u8 ⟨h8, s8, k8⟩ => ?_)
  have k18 := keep_same (keep_same (keep_same (keep_same (keep_same (keep_same (keep_same k1 k2) k3) k4) k5)
    k6) k7) k8
  have hdx8 : u8.gpr .x2 = K + BitVec.ofNat 64 (64 * hh) := by rw [k18.gpr _ (by decide), hdx]
  have hsi8 : u8.gpr .x1 = s.gpr .x1 := k18.gpr _ (by decide)
  refine WP.mono_syms (WP.keep [.x1, .x2] (show WP isa (.block [.addImm .x .x2 .x2 64, .subImm .x .x1 .x1 1]) u8
      fun w => w.gpr .x2 = u8.gpr .x2 + BitVec.ofNat 64 64 ∧ w.gpr .x1 = u8.gpr .x1 - BitVec.ofNat 64 1 ∧
        w.mem = u8.mem ∧ w.rd = u8.rd ∧ w.wr = u8.wr by crun) rfl rfl (by decide))
    fun w ⟨⟨w2, w1, wm, wrd, wwr⟩, wk⟩ wsy => ?_
  have hst : (halfImpl st).2 = runX xLines (runZ zLines (runX xLines (runZ zLines st))) := rfl
  have hks : ws ++ (halfImpl st).1 = ws ++ keys4 aLines (runZ zLines st) ++
      keys4 bLines (runX xLines (runZ zLines st)) ++ keys4 cLines (runZ zLines (runX xLines (runZ zLines st))) ++
      keys4 dLines (runX xLines (runZ zLines (runX xLines (runZ zLines st)))) := by
    simp only [halfImpl, List.append_assoc]
  rw [hst, hks]
  refine ⟨h8.update (wk.gpr _ (by decide)) (by rw [wm]; exact h8.mem) h8.len wrd wwr wsy, ?_,
    by rw [w1, hsi8], by rw [wsy, s8, s7, s6, s5, s4, s3, s2, s1], keep_same (keep_widen k18) (wk.mono)⟩
  rw [w2, hdx8, Proof.Cast5.add_ofNat_add, Nat.mul_succ]

end VG.Proof.Cast5.AArch64

end

end


/-!
# CAST5 key expansion on AArch64

`expandKey` pads the key with zeros into `x` (§2.5), then runs both halves of
§2.4 (`expandKey_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_byte (m : Mem) (c : Addr) {d e : Nat} (hd : d + 8 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (BitVec.setWidth 64 (0 : BitVec 16))) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 8 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

theorem zero_ok (s : State) (key : Addr) (hw : InRegions s.wr (s.gpr .x3) 64) :
    WP isa (.block [.movz .x .x9 0 0, .str .x .x9 .x3 xOff, .str .x .x9 .x3 (xOff + 8),
      .addImm .x .x4 .x3 xOff]) s fun u =>
      CInv s.mem key (s.gpr .x3) 0 u.mem ∧ u.gpr .x4 = s.gpr .x3 + BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .x4 → r ≠ .x9 → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms := by
  have h16 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 16) 8 := CallLay.inRegions_sub hw (by decide) (by decide)
  have h24 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 24) 8 := CallLay.inRegions_sub hw (by decide) (by decide)
  unfold xOff
  crun [h16, h24, Nat.reduceAdd]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, fun r h4 h9 => ?_⟩
  · rw [zero_byte _ _ (by decide) (by omega_using [hi]), zero_byte _ _ (by decide) (by omega_using [hi])]
    split <;> split <;> first | rfl | omega
  · rw [zero_byte _ _ (by decide) (by omega_using [hi]), zero_byte _ _ (by decide) (by omega_using [hi]), ite_eq_right (by omega_using []),
      ite_eq_right (by omega_using [])]
  · exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  · simp only [h4, h9, ite_false]

theorem add_one' (p : Addr) (a : Nat) : p + BitVec.ofNat 64 a + 1#64 = p + BitVec.ofNat 64 (a + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem copyStep_ok (u : State) {m0 : Mem} {key c : Addr} {j : Nat} (hj : j < 16) (hI : CInv m0 key c j u.mem)
    (hdi : u.gpr .x0 = key + BitVec.ofNat 64 j) (hax : u.gpr .x4 = c + BitVec.ofNat 64 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (key + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (c + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (key + BitVec.ofNat 64 j) = m0 (key + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 key c (j + 1) v.mem ∧ v.gpr .x0 = key + BitVec.ofNat 64 (j + 1) ∧
      v.gpr .x4 = c + BitVec.ofNat 64 (16 + (j + 1)) ∧ v.gpr .x1 = u.gpr .x1 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x4 → r ≠ .x0 → r ≠ .x1 → r ≠ .x9 → v.gpr r = u.gpr r) ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms := by
  have hr' : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 0) 1 := by rw [BitVec.add_zero, hdi]; exact hr
  have hw' : InRegions u.wr (u.gpr .x4 + BitVec.ofNat 64 0) 1 := by rw [BitVec.add_zero, hax]; exact hw
  have hk' : u.mem (u.gpr .x0 + BitVec.ofNat 64 0) = m0 (key + BitVec.ofNat 64 j) := by
    rw [BitVec.add_zero, hdi]; exact hk
  unfold copyStep
  crun [hr', hw', hk']
  simp only [BitVec.add_zero, hdi, hax, add_one']
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, trivial, by rw [Nat.add_assoc], fun r h1 h2 h3 h4 => ?_⟩
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
  rd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.syms s5678Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .x2, 128⟩, ⟨s.gpr .x3, 256⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s5678Sym + BitVec.ofNat 64 (8 * i)) 64 = s5678.getD i 0
  fitT : (s.syms s5678Sym).toNat + 4096 ≤ 2 ^ 64
  dTK : Region.Disjoint ⟨s.syms s5678Sym, 4096⟩ ⟨s.gpr .x2, 128⟩
  dTS : Region.Disjoint ⟨s.syms s5678Sym, 4096⟩ ⟨s.gpr .x3, 256⟩
  dkK : Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x2, 128⟩
  dkS : Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x3, 256⟩
  dKS : Region.Disjoint ⟨s.gpr .x2, 128⟩ ⟨s.gpr .x3, 256⟩
  fk : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  fK : (s.gpr .x2).toNat + 128 ≤ 2 ^ 64
  fS : (s.gpr .x3).toNat + 256 ≤ 2 ^ 64
  len : 5 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 16

theorem expandKey_ok (s : State) (h : KPre s) :
    WP isa expandKey s fun u =>
      Spec.Cast5.scheduleAt u.mem (s.gpr .x2) =
        Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) := by
  obtain ⟨n, hn⟩ : ∃ n, (s.gpr .x1).toNat = n := ⟨_, rfl⟩
  obtain ⟨key, hkey⟩ : ∃ key, s.gpr .x0 = key := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, s.gpr .x3 = c := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, s.gpr .x2 = K := ⟨_, rfl⟩
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
  have hsi0 : u0.gpr .x1 = BitVec.ofNat 64 n := by
    rw [g0 _ (by decide) (by decide), ← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (wp_countdown (cnt := .x1) (N := n) (by omega_using [hn]) (by omega_using [hl])
    (fun j u => CInv s.mem key c j u.mem ∧ u.gpr .x0 = key + BitVec.ofNat 64 j ∧
      u.gpr .x4 = c + BitVec.ofNat 64 (16 + j) ∧ (∀ r, r ∉ [Reg.x4, .x0, .x1, .x9] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms)
    (fun j hj u ⟨cu, du, au, gu, rdu, wru, syu⟩ _ => WP.mono (copyStep_ok u (by omega_using [hl, hj]) cu du au
      (by rw [rdu, wru]; exact CallLay.inRegions_sub hrK (by omega_using [hj]) (by omega_using [hn]))
      (by rw [wru]; exact CallLay.inRegions_sub hw64 (by omega_using [hl, hj]) (by decide))
      (hkb j hj u.mem cu.fr))
      fun v ⟨cv, dv, av, sv, gv, rdv, wrv, syv⟩ => ⟨⟨cv, dv, av, fun r hr => ?keepStep, rdv.trans rdu,
        wrv.trans wru, syv.trans syu⟩, sv⟩)
    ⟨c0, by rw [g0 _ (by decide) (by decide), hkey, BitVec.add_zero], by rw [ax0], fun r hr => ?keep0, rd0,
      wr0, sy0⟩ hsi0) fun u hu => ?rest)
  case keepStep =>
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [gv r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2, gu r hr]
  case keep0 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g0 r hr.1 hr.2.2.2
  case rest =>
    obtain ⟨cu, -, -, gu, rdu, wru, syu⟩ := hu
    refine WP.seq (WP.mono_syms (show WP isa (.block [.movz .x .x1 2 0]) u fun v =>
        v.gpr .x1 = BitVec.ofNat 64 2 ∧ v.mem = u.mem ∧ (∀ r, r ≠ .x1 → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
          v.wr = u.wr by
      crun
      exact ⟨rfl, fun r hr => ite_eq_right hr⟩) fun u1 ⟨si1, m1, g1, rd1, wr1⟩ sy1 => ?_)
    have g1s (r : Reg) (hr : r ∉ [Reg.x4, .x0, .x1, .x9]) : u1.gpr r = s.gpr r := by
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
    refine WP.mono (wp_countdown (cnt := .x1) (N := 2) (by decide) (by decide)
      (fun hh v => KS s.mem c K v (halves st0 hh).1 (halves st0 hh).2 ∧
        v.gpr .x2 = K + BitVec.ofNat 64 (64 * hh))
      (fun hh hh2 v ⟨kv, dv⟩ _ => WP.mono (half_ok kv dv (halves_length st0 hh) hh2)
        fun w ⟨kw, dw, sw, _, _⟩ => ⟨⟨kw, dw⟩, sw⟩)
      ⟨ks0, by rw [g1s _ (by decide), hK, Nat.mul_zero, BitVec.add_zero]⟩ si1) fun v ⟨kv, _⟩ => ?_
    rw [hK, hkey, hn, scheduleAt_keys kv.mem.keys (halves_length st0 2), Proof.Cast5.expandKey_eq _ st0.z, halves_two]

end VG.Proof.Cast5.AArch64
