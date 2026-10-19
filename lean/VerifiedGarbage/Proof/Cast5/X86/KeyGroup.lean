module

public import VerifiedGarbage.Proof.Cast5.X86.KeyLine
import VerifiedGarbage.Proof.Cast5.X86.Round
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseTaint

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
  rw [Mem.readW_writeW_sep (Offset.sep c (by unfold extraOff at *; omega) (by unfold extraOff; omega)
    (by unfold extraOff at *; omega)) (by decide)]
  exact h j hj

/-- `Extras` after a write elsewhere. -/
theorem Extras.write_disj {m : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {a : Addr}
    {w : Nat} (v : BitVec w) (hd : Region.Disjoint ⟨c, 64⟩ ⟨a, w / 8⟩) :
    Extras (m.writeW a v) c f := fun j hj => by
  rw [Mem.readW_writeW_sep (hd.sep (Offset.contains_base c (by unfold extraOff; omega)
    (by unfold extraOff; omega)) (Region.contains_self _ _)) (by decide)]
  exact h j hj

/-- `Extras` after a frame apart from them. -/
theorem Extras.frame {m m' : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {B : Region}
    (hf : Frame [B] m m') (hd : Region.Disjoint ⟨c, 64⟩ B) : Extras m' c f := fun j hj => by
  rw [hf.readW (r := ⟨c, 64⟩) (Offset.contains_base c (by unfold extraOff; omega) (by unfold extraOff; omega))
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
      (Offset.contains_base _ (by omega) (by have := h.fitT; omega)) (fun r hr => ?_) (by decide)]
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
      sbox l.extra.1 (st.get l.extra.2) := by rw [hE _ (by omega), hx]
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
  have hw : InRegions u.wr (addr S (off a + 4 * q)) 4 := slot_wr hu.fitS hu.wS (by omega)
  refine WP.mono (storeQuad_ok u hu.si a q uax hw) fun v ⟨vm, vg, vrd, vwr, vsy⟩ => ?_
  have k := KMem.quad hu.mem.kmem hu.dKS64 hu.len a hq (lineVal st l)
  rw [← addr_off hu.fitS _ (by omega), ← vm] at k
  refine ⟨hu.update (vg _ (by decide)) (vg _ (by decide)) (hu.mem.ofKMem k) hu.len vrd vwr vsy,
    by rw [vm, addr_off hu.fitS _ (by omega)]; exact uE.write _ (by unfold extraOff; omega), by rw [vsy, usy],
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
    rw [hadr]; exact CallLay.inRegions_sub hu.wK (by omega) (by decide)
  refine WP.mono (storeKey_ok u (by rw [uk.gpr .edi (by decide), hdi]) k uax hw)
    fun v ⟨vm, vg, vrd, vwr, vsy⟩ => ?_
  rw [hadr] at vm
  have hd : Region.Disjoint ⟨S.setWidth 64, 64⟩ ⟨K + BitVec.ofNat 64 (4 * ws.length), 32 / 8⟩ :=
    (hu.dKS64.sub_left (Offset.sub_base K (by omega))).symm
  have km := KMem.key hu.mem.kmem hu.dKS64 hlen (lineVal st l)
  rw [← vm] at km
  refine ⟨hu.update (by rw [vg]) (by rw [vg]) (hu.mem.ofKMem km)
      (by rw [List.length_append, List.length_singleton]; omega) vrd vwr vsy,
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
    rw [List.length_append, List.length_take, show (keys4 ls st).length = 4 from rfl, Nat.min_eq_left (by omega)]
  refine WP.mono (lineK_ok hu uE hok ?_ (k := b + k) (by rw [uk.gpr .edi (by decide), hdi])
      (by rw [hE _ (by omega), hl, hlen]; congr 2; omega) (by rw [hl]; omega))
    fun v hv => WP.mono hv fun w ⟨hw, wE, wsy, wk⟩ => ?_
  · rw [exVal_sbox _ _ he.1 he.2, hex]
  · rw [take_keys4 _ _ hk, ← List.append_assoc]
    exact ⟨hw, wE, by rw [wsy, usy], uk.trans wk⟩

end VG.Proof.Cast5.X86
