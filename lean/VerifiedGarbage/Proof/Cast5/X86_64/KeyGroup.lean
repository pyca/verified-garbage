import VerifiedGarbage.Proof.Cast5.X86_64.KeyMem

/-!
# CAST5 key expansion on x86-64: groups of four lines

A group (`lines4`) makes its four extra lookups (`extras_ok`), then runs its
lines, each storing its value into `x` or `z` (`groupQ_ok`) or as the next
subkey (`groupK_ok`).
-/

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
  rw [h.mem.fr.readW (Offset.contains_base _ (by omega) (by omega)) h.dT (by decide)]
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

/-- The extra lookups of a group, from the bytes at `a`, `b`, `c`, `d`. -/
def exVal (st : XZ) (a b c d : Pos) : Nat → Spec.Cast5.Word
  | 0 => Spec.Cast5.S8 (st.get d)
  | 1 => Spec.Cast5.S7 (st.get c)
  | 2 => Spec.Cast5.S6 (st.get b)
  | _ => Spec.Cast5.S5 (st.get a)

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
    scr_rw hw (by obtain ⟨a', i'⟩ := q; have := off_lt a'; simp only [srcOff] at hq ⊢; omega)
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
      sbox l.extra.1 (st.get l.extra.2) := by rw [h.rc, hE _ (by omega), hx]
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
    rw [hu.rc]; exact scr_w hu.wS (by omega)
  refine WP.mono (storeQuad_ok u a q uax hw) fun v ⟨vm, vg, vrd, vwr, vsy⟩ => ?_
  rw [hu.rc] at vm
  refine ⟨hu.update (vg _ (by decide)) (by rw [vm]; exact hu.mem.quad hu.dKS hu.len a hq _) hu.len vrd vwr vsy,
    by rw [vm]; exact uE.write _ (by unfold extraOff; omega), by rw [vsy, usy],
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
    rw [hadr]; exact CallLay.inRegions_sub hu.wK (by omega) (by decide)
  refine WP.mono (storeKey_ok u k uax hw) fun v ⟨vm, vg, vrd, vwr, vsy⟩ => ?_
  rw [hadr] at vm
  have hd : Region.Disjoint ⟨c, 64⟩ ⟨K + BitVec.ofNat 64 (4 * ws.length), 32 / 8⟩ :=
    (hu.dKS.sub_left (Offset.sub_base K (by omega))).symm
  refine ⟨hu.update (by rw [vg]) (by rw [vm]; exact hu.mem.key hu.dKS hlen _)
      (by rw [List.length_append, List.length_singleton]; omega) vrd vwr vsy,
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

theorem exVal_sbox (st : XZ) (ls : List Impl.Cast5.Line) {e : Nat} (h5 : 5 ≤ e) (h8 : e ≤ 8) :
    exVal st (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8) (8 - e) =
      sbox e (st.get (extraOf ls e)) := by
  rcases (show e = 5 ∨ e = 6 ∨ e = 7 ∨ e = 8 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- The first `k` lines of a group storing into `a`. -/
def runQ (a : Arr) (ls : List Impl.Cast5.Line) (k : Nat) (st : XZ) : XZ :=
  (List.range k).foldl (fun s j => s.put a j (lineVal s (ls.getD j default))) st

theorem runQ_succ (a : Arr) (ls : List Impl.Cast5.Line) (k : Nat) (st : XZ) :
    runQ a ls (k + 1) st = (runQ a ls k st).put a k (lineVal (runQ a ls k st) (ls.getD k default)) := by
  simp only [runQ, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem get_put (st : XZ) (a : Arr) (q : Nat) (w : Spec.Cast5.Word) {p : Pos} (hp : p.1 ≠ a) :
    (st.put a q w).get p = st.get p := by
  obtain ⟨a', i⟩ := p
  cases a <;> cases a' <;> first | exact absurd rfl hp | rfl

theorem get_runQ (a : Arr) (ls : List Impl.Cast5.Line) (k : Nat) (st : XZ) {p : Pos} (hp : p.1 ≠ a) :
    (runQ a ls k st).get p = st.get p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runQ_succ, get_put _ _ _ _ hp, ih]

/-- What a group needs of its lines. -/
def GroupOk (a : Option Arr) (ls : List Impl.Cast5.Line) : Prop :=
  (∀ k < 4, lineOk (ls.getD k default) = true ∧
    extraOf ls (ls.getD k default).extra.1 = (ls.getD k default).extra.2 ∧
    a ≠ some (ls.getD k default).extra.2.1) ∧
  ∀ e < 4, (extraOf ls (5 + e)).2 < 16

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

theorem take_keys4 (ls : List Impl.Cast5.Line) (st : XZ) {k : Nat} (hk : k < 4) :
    (keys4 ls st).take (k + 1) = (keys4 ls st).take k ++ [lineVal st (ls.getD k default)] := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

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
    rw [List.length_append, List.length_take, show (keys4 ls st).length = 4 from rfl, Nat.min_eq_left (by omega)]
  refine WP.mono (lineK_ok hu uE hok ?_ (k := b + k) (b := 64 * hh) (by rw [uk.1 _ (by decide), hdx])
      (by rw [hl, hlen]; omega) (by rw [hl]; omega)) fun v hv => WP.mono hv fun w ⟨hw, wE, wsy, wk⟩ => ?_
  · rw [exVal_sbox _ _ he.1 he.2, hex]
  · rw [take_keys4 _ _ hk, ← List.append_assoc]
    exact ⟨hw, wE, by rw [wsy, usy], keep_same uk wk⟩

end VG.Proof.Cast5.X86_64
