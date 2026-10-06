import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop
import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma

/-!
# Ed25519 verification with AVX512_IFMA: adding a table entry in the lanes

A cached table entry `[Y - X, Y + X, 2dT, 2Z]` of `q`, at a public offset of
the scratch, is loaded a row at a time (`vrows`), split into limbs (`esplit`)
and added to the point in the lanes (`vadd`): the lanes then hold
`pointAdd P q` for the point `P` they held.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
  VG.Proof.Ed25519.X86_64 Edwards
open VG.Impl.X25519.X86_64.Ifma (KM y)
open VG.Proof.X25519.X86_64.Ifma (Sym symOf symOf_eq lanes fe5 fe5_congr limbNat limbNat_lv
  envOK_of envOf envOf_m lt64 run_ok vm vm_gpr vm_rd vm_wr Ctx CConsts mq)
open VG.Proof.X25519.X86_64 (Outside F off)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw qw_load)

/-! ## The rows into limbs -/

def esplitS : Sym := symOf esplit

theorem esplitS_regs (E : VG.Proof.X25519.X86_64.Ifma.Env) : ∀ j < 5, ∀ l < 4, (esplitS.reg (5 + j)).nat E l =
    limbNat (fun k => E.v (11 + l) k) (E.m KM l) j := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem esplitS_ok : ∀ j < 5, ∀ l < 4, (esplitS.reg (5 + j)).ok eloadB l = true ∧
    (esplitS.reg (5 + j)).bnd eloadB l < 2 ^ 52 := by
  decide +kernel

theorem esplitS_keep : ∀ r < 5, esplitS.reg r = .reg r := by decide +kernel
theorem esplitS_st : esplitS.st = [] := by decide +kernel

/-- `esplit`: the words of row `l` (in `ymm (11 + l)`) into the limbs of lane `l` of `ymm5–ymm9`. -/
theorem esplit_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : CConsts s.mem base) :
    WP isa (.block esplit) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 5 l i = limbNat (fun k => (qw s (xr (11 + l)) k).toNat) (2 ^ 51 - 1) i ∧
        lanes s' 5 l i < 2 ^ 52) ∧
      (∀ r < 5, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := envOK_of (B := eloadB) hs (fun _ _ _ => lt64 _) (fun _ => rfl) (fun d l hl => by
      simp only [eloadB]
      split
      · subst_vars; rw [hk.km l hl]
      · exact lt64 _) (fun _ _ _ => Nat.zero_le _)
  have e : Sym.init.run esplit = some esplitS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ⟨h.eq, by rw [h.mem, esplitS_st]; rfl, fun l hl i hi => ?_,
    fun r hr l hl => h.keep (by omega) hl (esplitS_keep r hr)⟩
  obtain ⟨o, b⟩ := esplitS_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega) hl o
  simp only [lanes] at e ⊢
  refine ⟨?_, by omega⟩
  rw [e, esplitS_regs _ i hi l hl, envOf_m hs, hk.km l hl]
  rfl

/-! ## The rows -/

/-- Row `j` of the entry at `rax = base + o` into `ymm (11 + j)`. -/
theorem vrow_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (ho : o + 128 ≤ 8192) (j : Nat) (hj : j < 4) :
    WP isa (.block [.vmovdquLoad .l256 (y (11 + j)) (VG.Impl.X25519.X86_64.at_ .rax (32 * j))]) s fun t =>
      (∀ k < 4, qw t (xr (11 + j)) k = mq s.mem base (o + 32 * j + 8 * k)) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ xr (11 + j) → ∀ k < 4, qw t r k = qw s r k) := by
  have hea : off (s.gpr .rax) (32 * j) = base + BitVec.ofNat 64 (o + 32 * j) := by
    rw [hp, off, off, Offset.add_add]
  have hr : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 32 * j)) 32 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have hy : y (11 + j) = xr (11 + j) := y_xr _ (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X25519.X86_64.ea_at, hea,
    State.load256, hr, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, rfl, rfl, rfl, rfl, fun r hr k hk => ?_⟩
  · rw [qw_load _ _ _ _ hk, hy, ite_eq_left_iff.mpr (fun h => absurd rfl h), mq, Offset.add_add]
  · rw [qw_load _ _ _ _ hk, hy]; exact ite_eq_right_iff.mpr fun h => absurd h hr

theorem xr_ne : ∀ a < 16, ∀ b < 16, a ≠ b → xr a ≠ xr b := by decide

theorem vrowsPrefix_ok {base : Addr} {o : Nat} (ho : o + 128 ≤ 8192) :
    ∀ n ≤ 4, ∀ s : State, Scratch s base → s.gpr .rax = off base o →
    WP isa (.block ((List.range n).map fun j =>
        .vmovdquLoad .l256 (y (11 + j)) (VG.Impl.X25519.X86_64.at_ .rax (32 * j)))) s fun t =>
      (∀ l < n, ∀ k < 4, qw t (xr (11 + l)) k = mq s.mem base (o + 32 * l + 8 * k)) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r < 16, (∀ l < n, r ≠ 11 + l) → ∀ k < 4, qw t (xr r) k = qw s (xr r) k)
  | 0, _, s, _, _ => WP.block_nil ⟨fun l hl => absurd hl (Nat.not_lt_zero _), rfl, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | n + 1, hn, s, hs, hp => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (vrowsPrefix_ok ho n (by omega) s hs hp) fun a ⟨al, ag, am, ard, awr, ak⟩ => ?_
    have ha : Scratch a base := ⟨by rw [ag]; exact hs.rdi, by rw [awr]; exact hs.wr, hs.nowrap⟩
    refine WP.mono (vrow_ok ha (by rw [ag]; exact hp) ho n (by omega))
      fun t ⟨tl, tg, tm, trd, twr, tk⟩ => ⟨fun l hl k hk => ?_, tg.trans ag, tm.trans am, trd.trans ard,
        twr.trans awr, fun r hr hrl k hk => ?_⟩
    · by_cases h : l = n
      · subst h; rw [tl k hk, am]
      · rw [tk _ (xr_ne _ (by omega) _ (by omega) (by omega)) k hk, al l (by omega) k hk]
    · rw [tk _ (xr_ne _ hr _ (by omega) (hrl n (by omega))) k hk,
        ak r hr (fun l hl => hrl l (by omega)) k hk]

/-- `vrows`: the four rows of the entry at `rax = base + o` into `ymm11–ymm14`. -/
theorem vrows_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (ho : o + 128 ≤ 8192) :
    WP isa (.block vrows) s fun t =>
      (∀ l < 4, ∀ k < 4, qw t (xr (11 + l)) k = mq s.mem base (o + 32 * l + 8 * k)) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r < 11, ∀ k < 4, qw t (xr r) k = qw s (xr r) k) :=
  WP.mono (vrowsPrefix_ok ho 4 (by decide) s hs hp) fun _ ⟨tl, tg, tm, trd, twr, tk⟩ =>
    ⟨tl, tg, tm, trd, twr, fun r hr => tk r (by omega) (fun l hl => by omega)⟩

theorem limbNat_congr {w w' : Nat → Nat} {m : Nat} (h : ∀ k < 4, w k = w' k) (i : Nat) :
    limbNat w m i = limbNat w' m i := by
  rcases i with _ | _ | _ | _ | _ | _ <;>
    simp only [limbNat, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-- A field element's four words, split into limbs. -/
theorem fe5_words (m : Mem) (base : Addr) (d : Nat) :
    fe5 (limbNat (fun k => (mq m base (d + 8 * k)).toNat) (2 ^ 51 - 1)) = F m base d := by
  show VG.Proof.X25519.toFe _ = VG.Proof.X25519.toFe _
  rw [limbNat_lv _ (fun k _ => BitVec.isLt _)]
  rfl

/-- The entry at byte `o` of the scratch, `[Y - X, Y + X, 2dT, 2Z]` of `q`, added to the point in
the lanes. -/
theorem ventryAt_ok {s : State} {base : Addr} (hs : Scratch s base) (hk : EConsts s.mem base)
    (hx : Small s) {o : Nat} (hp : s.gpr .rax = off base o) (ho : o + 128 ≤ 8192)
    {q : Spec.Ed25519.Point} (hq : tablePoint s.mem base o = cache q) :
    WP isa (.block (vrows ++ (esplit ++ vadd))) s fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 1024 320 s.mem t.mem ∧ Small t ∧ lanePt t = Spec.Ed25519.pointAdd (lanePt s) q := by
  rw [WP.block_append_iff]
  refine WP.mono (vrows_ok hs hp ho) fun a ⟨al, ag, am, ard, awr, ak⟩ => ?_
  have ha : Scratch a base := ⟨by rw [ag]; exact hs.rdi, by rw [awr]; exact hs.wr, hs.nowrap⟩
  have hka : EConsts a.mem base := by rw [am]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (esplit_wp ha.rdi (ctx_of ha) hka.toCConsts) fun b ⟨vb, mb, ub, kb⟩ => ?_
  have hb : Scratch b base := ⟨by rw [vm_gpr vb]; exact ha.rdi, by rw [vm_wr vb]; exact ha.wr, hs.nowrap⟩
  have hkb : EConsts b.mem base := by rw [mb]; exact hka
  have l0 : ∀ l < 4, ∀ i < 5, lanes b 0 l i = lanes s 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]; rw [kb i hi l hl, ak i (by omega) l hl]
  have p0 : lanePt b = lanePt s := by
    simp only [lanePt]
    rw [fe5_congr (l0 0 (by decide)), fe5_congr (l0 1 (by decide)), fe5_congr (l0 2 (by decide)),
      fe5_congr (l0 3 (by decide))]
  have p5 : lanePt5 b = cache q := by
    have e : ∀ l < 4, fe5 (lanes b 5 l) = F s.mem base (o + 32 * l) := fun l hl => by
      rw [fe5_congr (fun i hi => (ub l hl i hi).1), ← fe5_words s.mem base (o + 32 * l)]
      exact fe5_congr fun i _ => limbNat_congr (fun k hk => by rw [al l hl k hk]) i
    rw [← hq]
    simp only [lanePt5, tablePoint]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    rfl
  refine WP.mono (vadd_wp hb.rdi (ctx_of hb) hkb (fun l hl i hi => by rw [l0 l hl i hi]; exact hx l hl i hi)
    (fun l hl i hi => (ub l hl i hi).2)) fun t ⟨tg, trd, twr, tou, tsm, tp⟩ => ?_
  refine ⟨by rw [tg, vm_gpr vb, ag], by rw [trd, vm_rd vb, ard], by rw [twr, vm_wr vb, awr], ?_, tsm, ?_⟩
  · rw [mb, am] at tou; exact tou
  · rw [tp, p0, p5, vAddPt_cache]

/-! ## A digit's entry -/

/-- What a window in the lanes may change: the registers a window may but `r11` (the saved
MXCSR), the vector registers, and the products' operands (bytes 1024–1343 of the scratch). -/
structure LKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.X25519.X86_64.clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  r11 : t.gpr .r11 = s.gpr .r11
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 1024 320 s.mem t.mem

theorem LKeep.refl (base : Addr) (s : State) : LKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem LKeep.trans {base : Addr} {s t u : State} (h : LKeep base s t) (k : LKeep base t u) :
    LKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.r11.trans h.r11, k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem LKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : VG.Proof.X25519.X86_64.Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ (r ∈ VG.Proof.X25519.X86_64.clob ∧ r ≠ .r11)) :
    LKeep base s t :=
  ⟨fun r hc hb hs => h.1 r fun hm => by
      rcases hrs r hm with rfl | rfl | ⟨hm', _⟩
      · exact hb rfl
      · exact hs rfl
      · exact hc hm',
    h.1 _ fun hm => by rcases hrs _ hm with h | h | ⟨_, h⟩ <;> exact absurd h (by decide),
    h.2.2.1, h.2.2.2, by rw [h.2.1]; exact Outside.refl _ _ _ _⟩

theorem LKeep.win {base : Addr} {s t : State} (h : LKeep base s t) : WinKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem LKeep.scratch {base : Addr} {s t : State} (h : LKeep base s t) (hs : Scratch s base) :
    Scratch t base := h.win.scratch hs

theorem LKeep.consts {base : Addr} {s t : State} (h : LKeep base s t) (hk : EConsts s.mem base) :
    EConsts t.mem base := hk.outside h.mem

/-- The slots below byte 1024 (`d`, in slot 16, among them) are kept. -/
theorem LKeep.slot {base : Addr} {s t : State} (h : LKeep base s t) (i : Slot) :
    env t.mem base i = env s.mem base i :=
  Outside_F h.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))

theorem tableAddr_scal (o : Nat) : scalCode (.block (tableAddr o) : Prog isa) = true := rfl

theorem lanePt_vec {s t : State} (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) :
    lanePt t = lanePt s ∧ (Small s → Small t) :=
  lanes0_eq (lanes0_vec hx hy)

/-- A digit `v`'s entry of the cached table at byte `o`, added to the point in the lanes. -/
theorem vaddDigit_ok {s : State} {base : Addr} (hs : Scratch s base) (hk : EConsts s.mem base)
    (hx : Small s) {o : Nat} (hlo : 1888 ≤ o) (hhi : o + 1920 ≤ 8192) {X a : EPoint dZ}
    (htab : TableOf cache s.mem base o X) (v : Nat) (hv : v < 16) (hc : s.gpr .rbx = BitVec.ofNat 64 v)
    (hz : s.zf = some (decide (v = 0))) (ha : Rep (lanePt s) a) :
    WP isa (vaddDigit o) s fun t => Rep (lanePt t) (a + v • X) ∧ Small t ∧ LKeep base s t := by
  rw [vaddDigit]
  refine WP.ite (!decide (v = 0)) (by simp only [eval, hz, Option.map_some]) (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := by simpa using h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (WP.vecKeep (by decide) (accumulateDec_ok s n hc)) fun b ⟨⟨bc, kb⟩, bx, bhy⟩ => ?_
    have hsb : Scratch b base := hs.of_keeps kb (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (WP.vecKeep (tableAddr_scal o) (tableAddr_ok hsb.rdi o n (by omega) bc))
      fun c ⟨⟨cp, kc⟩, cx, chy⟩ => ?_
    have hsc : Scratch c base := hsb.of_keeps kc (by decide)
    have hm : c.mem = s.mem := kc.2.1.trans kb.2.1
    obtain ⟨q, hq, hr⟩ := htab n (by omega)
    obtain ⟨pc, sc⟩ := lanePt_vec (cx.trans bx) (chy.trans bhy)
    refine WP.mono (ventryAt_ok (q := q) hsc (by rw [hm]; exact hk) (sc hx) cp (by omega) (by rw [hm]; exact hq))
      fun t ⟨tg, trd, twr, tou, tsm, tp⟩ => ⟨?_, tsm, ?_⟩
    · rw [tp, pc]; exact pointAdd_rep ha hr
    · refine (LKeep.of_keeps kb (by decide)).trans ((LKeep.of_keeps kc (by decide)).trans
        ⟨fun r _ _ _ => by rw [tg], by rw [tg], trd, twr, tou⟩)
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    exact WP.block_nil ⟨by rw [zero_smul, add_zero]; exact ha, hx, LKeep.refl _ _⟩

end VG.Proof.Ed25519.X86_64.Ifma
