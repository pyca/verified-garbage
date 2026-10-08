import VerifiedGarbage.Proof.Cast5.AArch64.KeyLine

/-!
# CAST5 key expansion on AArch64: groups of four lines

A group (`lines4`) makes its four extra lookups into `v6` (`extras_ok`),
then runs its lines, each storing its value into `x` or `z` (`groupQ_ok`) or
as the next subkey (`groupK_ok`).
-/

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
  rw [h.mem.fr.readW (Offset.contains_base _ (by omega) (by omega)) h.dT (by decide)]
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
    CallLay.inRegions_sub h.ws (by obtain ⟨a', i'⟩ := q; have := off_lt a'; simp only [srcOff] at hq ⊢; omega)
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
        obtain ⟨n1, n2, n3, n4, n5⟩ := pv_ne r hr
        rw [wk.vcs r hr, vk.v r n1 n2 n3 n4 n5, uk.vcs r hr]⟩⟩
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
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
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
    cases a <;> simp only [off, xOff, zOff] <;> omega
  unfold storeQuad
  crun [hax, hw, ho, rev32_eq]
  exact fun r hr => ite_eq_right hr

theorem storeKey_ok (u : State) {k : Nat} (hk : k < 32) {v : Spec.Cast5.Word}
    (hax : u.gpr .x0 = v.setWidth 64)
    (hw : InRegions u.wr (u.gpr .x2 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (storeKey k)) u fun w =>
      w.mem = u.mem.writeW (u.gpr .x2 + BitVec.ofNat 64 (4 * k)) v ∧ w.gpr = u.gpr ∧ w.rd = u.rd ∧
        w.wr = u.wr ∧ w.v = u.v := by
  have ho : (4 * k) % 4 = 0 ∧ 4 * k < 16384 := ⟨by omega, by omega⟩
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
    rw [hE, vword_L _ (by omega), hx]
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
    rw [hu.rc]; exact CallLay.inRegions_sub hu.wS (by omega) (by decide)
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
    rw [hadr]; exact CallLay.inRegions_sub hu.wK (by omega) (by decide)
  refine WP.mono_syms (WP.keep [] (storeKey_ok u hk ux0 hw) rfl rfl rfl)
    fun v ⟨⟨vm, vg, vrd, vwr, vv⟩, vk⟩ vsy => ?_
  rw [hadr] at vm
  refine ⟨hu.update (by rw [vg]) (by rw [vm]; exact hu.mem.key hu.dKS hlen _)
      (by rw [List.length_append, List.length_singleton]; omega) vrd vwr vsy,
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
    rw [List.length_append, List.length_take, show (keys4 ls st).length = 4 from rfl, Nat.min_eq_left (by omega)]
  refine WP.mono (lineK_ok hu uE hok ?_ (k := b + k) (b := 64 * hh) (by omega) (by rw [uk.gpr _ (by decide), hdx])
      (by rw [hl, hlen]; omega) (by rw [hl]; omega)) fun v hv => WP.mono hv fun w ⟨hw, wE, wsy, wk⟩ => ?_
  · rw [exVal_sbox _ _ he.1 he.2, hex]
  · rw [take_keys4 _ _ hk, ← List.append_assoc]
    exact ⟨hw, wE, by rw [wsy, usy], keep_same uk wk⟩

end VG.Proof.Cast5.AArch64
