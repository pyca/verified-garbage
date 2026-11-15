module

import VerifiedGarbage.Proof.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop
public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma
public import VerifiedGarbage.Proof.Ed25519.X86_64.WindowStep
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombStage
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.Double4
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part1
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.X25519.X86_64.Setup
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.X86_64Scal
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowDigits
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! ### `Ed25519.X86_64.Ifma.VerifyAdd`, which only this module used -/

section

/-!
# Ed25519 verification with AVX512_IFMA: adding a table entry in the lanes

A cached table entry `[Y - X, Y + X, 2dT, 2Z]` of `q`, at a public offset of
the scratch, is loaded a row at a time (`vrows`), split into limbs (`esplit`)
and added to the point in the lanes (`vadd`): the lanes then hold
`pointAdd P q` for the point `P` they held.
-/

@[expose] public section

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
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
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
    fun r hr l hl => h.keep (by omega_using [hr]) hl (esplitS_keep r hr)⟩
  obtain ⟨o, b⟩ := esplitS_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_using [hi]) hl o
  simp only [lanes] at e ⊢
  refine ⟨?_, by omega_using [b, be]⟩
  rw [e, esplitS_regs _ i hi l hl, envOf_m hs, hk.km l hl]
  rfl

/-! ## The rows -/

/-- Row `j` of the entry at `rax = E` into `ymm (11 + j)`. -/
theorem vrow_ok {s : State} {E : Addr} (hp : s.gpr .rax = E) (j : Nat) (hj : j < 4)
    (hr : InRegions (s.rd ++ s.wr) (off E (32 * j)) 32) :
    WP isa (.block [.vmovdquLoad .l256 (y (11 + j)) (VG.Impl.X25519.X86_64.at_ .rax (32 * j))]) s fun t =>
      (∀ k < 4, qw t (xr (11 + j)) k = mq s.mem E (32 * j + 8 * k)) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ xr (11 + j) → ∀ k < 4, qw t r k = qw s r k) := by
  have hea : off (s.gpr .rax) (32 * j) = off E (32 * j) := by rw [hp]
  have hy : y (11 + j) = xr (11 + j) := y_xr _ (by omega_using [hj])
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X25519.X86_64.ea_at, hea,
    State.load256, hr, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, rfl, rfl, rfl, rfl, fun r hr k hk => ?_⟩
  · rw [qw_load _ _ _ _ hk, hy, ite_eq_left_iff.mpr (fun h => absurd rfl h), mq, off, Offset.add_add]
  · rw [qw_load _ _ _ _ hk, hy]; exact ite_eq_right_iff.mpr fun h => absurd h hr

theorem xr_ne : ∀ a < 16, ∀ b < 16, a ≠ b → xr a ≠ xr b := by decide

theorem vrowsPrefix_ok {E : Addr} :
    ∀ n ≤ 4, ∀ s : State, s.gpr .rax = E →
    (∀ d, d + 32 ≤ 128 → InRegions (s.rd ++ s.wr) (off E d) 32) →
    WP isa (.block ((List.range n).map fun j =>
        .vmovdquLoad .l256 (y (11 + j)) (VG.Impl.X25519.X86_64.at_ .rax (32 * j)))) s fun t =>
      (∀ l < n, ∀ k < 4, qw t (xr (11 + l)) k = mq s.mem E (32 * l + 8 * k)) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r < 16, (∀ l < n, r ≠ 11 + l) → ∀ k < 4, qw t (xr r) k = qw s (xr r) k)
  | 0, _, s, _, _ => WP.block_nil ⟨fun l hl => absurd hl (Nat.not_lt_zero _), rfl, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | n + 1, hn, s, hp, hr => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (vrowsPrefix_ok n (by omega_using [hn]) s hp hr) fun a ⟨al, ag, am, ard, awr, ak⟩ => ?_
    refine WP.mono (vrow_ok (E := E) (by rw [ag]; exact hp) n (by omega_using [hn])
      (by rw [ard, awr]; exact hr (32 * n) (by omega_using [hn])))
      fun t ⟨tl, tg, tm, trd, twr, tk⟩ => ⟨fun l hl k hk => ?_, tg.trans ag, tm.trans am, trd.trans ard,
        twr.trans awr, fun r hr hrl k hk => ?_⟩
    · by_cases h : l = n
      · subst h; rw [tl k hk, am]
      · rw [tk _ (xr_ne _ (by omega_using [hn, hl]) _ (by omega_using [hn]) (by omega_using [h])) k hk, al l (by omega_using [hl, h]) k hk]
    · rw [tk _ (xr_ne _ hr _ (by omega_using [hn]) (hrl n (by omega_using []))) k hk,
        ak r hr (fun l hl => hrl l (by omega_using [hl])) k hk]

/-- `vrows`: the four rows of the entry at `rax = E` into `ymm11–ymm14`. -/
theorem vrows_ok {s : State} {E : Addr} (hp : s.gpr .rax = E)
    (hr : ∀ d, d + 32 ≤ 128 → InRegions (s.rd ++ s.wr) (off E d) 32) :
    WP isa (.block vrows) s fun t =>
      (∀ l < 4, ∀ k < 4, qw t (xr (11 + l)) k = mq s.mem E (32 * l + 8 * k)) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r < 11, ∀ k < 4, qw t (xr r) k = qw s (xr r) k) :=
  WP.mono (vrowsPrefix_ok 4 (by decide) s hp hr) fun _ ⟨tl, tg, tm, trd, twr, tk⟩ =>
    ⟨tl, tg, tm, trd, twr, fun r hr => tk r (by omega_using [hr]) (fun l hl => by omega_using [hr])⟩

theorem F_off (m : Mem) (base : Addr) (o d : Nat) : F m (off base o) d = F m base (o + d) := by
  simp only [F, VG.Proof.X25519.X86_64.fe, VG.Proof.X25519.X86_64.word, off, Offset.add_add,
    Nat.add_assoc]

/-- A table entry in the scratch, as an entry at its address. -/
theorem tablePoint_off (m : Mem) (base : Addr) (o : Nat) :
    tablePoint m (off base o) 0 = tablePoint m base o := by
  simp only [tablePoint, F_off, Nat.zero_add, Nat.add_zero]

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

/-- The entry at `E`, readable, `[Y - X, Y + X, 2dT, 2Z]` of `q`, added to the point in the
lanes. -/
theorem ventryAt_ok {s : State} {base E : Addr} (hs : Scratch s base) (hk : EConsts s.mem base)
    (hx : Small s) (hp : s.gpr .rax = E)
    (hr : ∀ d, d + 32 ≤ 128 → InRegions (s.rd ++ s.wr) (off E d) 32)
    {q : Spec.Ed25519.Point} (hq : tablePoint s.mem E 0 = cache q) :
    WP isa (.block (vrows ++ (esplit ++ vadd))) s fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 1024 320 s.mem t.mem ∧ Small t ∧ lanePt t = Spec.Ed25519.pointAdd (lanePt s) q := by
  rw [WP.block_append_iff]
  refine WP.mono (vrows_ok hp hr) fun a ⟨al, ag, am, ard, awr, ak⟩ => ?_
  have ha : Scratch a base := ⟨by rw [ag]; exact hs.rdi, by rw [awr]; exact hs.wr, hs.nowrap⟩
  have hka : EConsts a.mem base := by rw [am]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (esplit_wp ha.rdi (ctx_of ha) hka.toCConsts) fun b ⟨vb, mb, ub, kb⟩ => ?_
  have hb : Scratch b base := ⟨by rw [vm_gpr vb]; exact ha.rdi, by rw [vm_wr vb]; exact ha.wr, hs.nowrap⟩
  have hkb : EConsts b.mem base := by rw [mb]; exact hka
  have l0 : ∀ l < 4, ∀ i < 5, lanes b 0 l i = lanes s 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]; rw [kb i hi l hl, ak i (by omega_using [hi]) l hl]
  have p0 : lanePt b = lanePt s := by
    simp only [lanePt]
    rw [fe5_congr (l0 0 (by decide)), fe5_congr (l0 1 (by decide)), fe5_congr (l0 2 (by decide)),
      fe5_congr (l0 3 (by decide))]
  have p5 : lanePt5 b = cache q := by
    have e : ∀ l < 4, fe5 (lanes b 5 l) = F s.mem E (32 * l) := fun l hl => by
      rw [fe5_congr (fun i hi => (ub l hl i hi).1), ← fe5_words s.mem E (32 * l)]
      exact fe5_congr fun i _ => limbNat_congr (fun k hk => by rw [al l hl k hk]) i
    rw [← hq]
    simp only [lanePt5, tablePoint]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
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

/-- The slots below byte 1024 (`d`, in slot 16, among them) are kept. -/
theorem LKeep.slot {base : Addr} {s t : State} (h : LKeep base s t) (i : Slot) :
    env t.mem base i = env s.mem base i :=
  Outside_F h.mem (by simp only [offset]; omega_using []) (Or.inl (by simp only [offset]; omega_using []))

theorem tableAddr_scal (o : Nat) : scalCode (.block (tableAddr o) : Prog isa) = true := rfl

theorem lanePt_vec {s t : State} (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) :
    lanePt t = lanePt s ∧ (Small s → Small t) :=
  lanes0_eq (lanes0_vec hx hy)

/-- A digit `v`'s entry `v - 1` of the cached table at byte `o`, added to the point in the lanes. -/
theorem vaddDigit_ok {s : State} {base : Addr} (hs : Scratch s base) (hk : EConsts s.mem base)
    (hx : Small s) {o : Nat} (hlo : 1888 ≤ o) (hhi : o + 2048 ≤ 8192) {X a : EPoint dZ}
    (htab : TableOf cache s.mem base o X) (v : Nat) (hv : v ≤ 16) (hc : s.gpr .rbx = BitVec.ofNat 64 v)
    (hz : s.zf = some (decide (v = 0))) (ha : Rep (lanePt s) a) :
    WP isa (vaddDigit o) s fun t => Rep (lanePt t) (a + (Recode.dec v) • X) ∧ Small t ∧ LKeep base s t := by
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
    refine WP.mono (ventryAt_ok (q := q) hsc (by rw [hm]; exact hk) (sc hx) cp
      (fun d hd => ⟨_, List.mem_append_right _ hsc.wr, by
        simp only [off, Offset.add_add]; exact Offset.contains_base _ (by omega) (by have := hsc.nowrap; omega)⟩)
      (by rw [hm, tablePoint_off]; exact hq))
      fun t ⟨tg, trd, twr, tou, tsm, tp⟩ => ⟨?_, tsm, ?_⟩
    · rw [tp, pc]; exact pointAdd_rep ha hr
    · refine (LKeep.of_keeps kb (by decide)).trans ((LKeep.of_keeps kc (by decide)).trans
        ⟨fun r _ _ _ => by rw [tg], by rw [tg], trd, twr, tou⟩)
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    exact WP.block_nil ⟨by simpa [Recode.dec] using ha, hx, LKeep.refl _ _⟩

theorem baseAddr_scal : scalCode (.block baseAddr : Prog isa) = true := rfl

/-- `S`'s digit `v`'s entry `v - 1` of the static at `T`, added to the point in the lanes. -/
theorem vaddBase_ok {s : State} {base T : Addr} (hs : Scratch s base) (hk : EConsts s.mem base)
    (hx : Small s) (hT : s.mem.readW (off base 7960) 64 = T) (ht : BaseTbl s base T) {a : EPoint dZ}
    (v : Nat) (hv : v ≤ 128) (hc : s.gpr .rbx = BitVec.ofNat 64 v)
    (hz : s.zf = some (decide (v = 0))) (ha : Rep (lanePt s) a) :
    WP isa vaddBase s fun t => Rep (lanePt t) (a + (Recode.dec v) • (-baseAff)) ∧ Small t ∧
      LKeep base s t := by
  rw [vaddBase]
  refine WP.ite (!decide (v = 0)) (by simp only [eval, hz, Option.map_some]) (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := by simpa using h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (WP.vecKeep (by decide) (accumulateDec_ok s n hc)) fun b ⟨⟨bc, kb⟩, bx, bhy⟩ => ?_
    have hsb : Scratch b base := hs.of_keeps kb (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (WP.vecKeep baseAddr_scal (baseAddr_ok (T := T) hsb (by rw [kb.2.1]; exact hT) n (by omega_using [hv]) bc))
      fun c ⟨⟨cp, kc⟩, cx, chy⟩ => ?_
    have hsc : Scratch c base := hsb.of_keeps kc (by decide)
    have hm : c.mem = s.mem := kc.2.1.trans kb.2.1
    obtain ⟨q, hq, hr⟩ := baseOddCached_ok n (by omega_using [hv])
    obtain ⟨pc, sc⟩ := lanePt_vec (cx.trans bx) (chy.trans bhy)
    refine WP.mono (ventryAt_ok (q := q) hsc (by rw [hm]; exact hk) (sc hx) cp
      (fun d hd => by
        rw [kc.2.2.1, kc.2.2.2, kb.2.2.1, kb.2.2.2]
        have := ht.read (128 * n + d) 32 (by omega_using [hv, hd])
        simp only [off, Offset.add_add] at this ⊢
        exact this)
      (by rw [hm, ht.entry n (by omega_using [hv]), hq]))
      fun t ⟨tg, trd, twr, tou, tsm, tp⟩ => ⟨?_, tsm, ?_⟩
    · rw [tp, pc]; exact pointAdd_rep ha hr
    · refine (LKeep.of_keeps kb (by decide)).trans ((LKeep.of_keeps kc (by decide)).trans
        ⟨fun r _ _ _ => by rw [tg], by rw [tg], trd, twr, tou⟩)
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    exact WP.block_nil ⟨by simpa [Recode.dec] using ha, hx, LKeep.refl _ _⟩

end VG.Proof.Ed25519.X86_64.Ifma

end

end


/-!
# Ed25519 verification with AVX512_IFMA: the windows in the lanes

A position of `Ifma.windows` is a doubling (`vdbl`) and its digits' additions (`vaddDigit`,
`vaddBase`), as one of `windows` is, with the point in the lanes, where every doubling
computes `T`: the invariants are `windows`' (`WindowSlide`), with the point in the lanes.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
  VG.Proof.Ed25519.X86_64 Edwards
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1)
open VG.Proof.X25519.X86_64 (Outside off clob Keeps)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr)
open VG.Proof.Poly1305.X86_64.Avx2 (qw)

/-- A block of scalar instructions keeps the vector registers. -/
theorem WP.vk {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hc : is.all scalarI = true := by decide) :
    WP isa (.block is) s fun t => Q t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi :=
  WP.vecKeep (c := .block is) hc h

/-- The constants are kept by anything that changes only bytes below them. -/
theorem EConsts.below {m m' : Mem} {base : Addr} (hk : EConsts m base) {o n : Nat}
    (h : Outside base o n m m') (hon : o + n ≤ 1664) : EConsts m' base := by
  have w : ∀ d, 1664 ≤ d → d + 8 ≤ 4096 →
      VG.Proof.X25519.X86_64.Ifma.mq m' base d = VG.Proof.X25519.X86_64.Ifma.mq m base d :=
    fun d h1 h2 => by
      rw [VG.Proof.X25519.X86_64.Ifma.mq_eq_word, VG.Proof.X25519.X86_64.Ifma.mq_eq_word]
      exact h.word (by omega_arith) (by omega_arith)
  refine ⟨⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩, fun l hl => ?_,
    fun l hl => ?_, fun l hl => ?_⟩
  · rw [w _ (by simp only [KM]; omega_arith) (by simp only [KM]; omega_arith)]; exact hk.km l hl
  · rw [w _ (by simp only [K19]; omega_arith) (by simp only [K19]; omega_arith)]; exact hk.k19 l hl
  · rw [w _ (by simp only [KB0]; omega_arith) (by simp only [KB0]; omega_arith)]; exact hk.kb0 l hl
  · rw [w _ (by simp only [KB1]; omega_arith) (by simp only [KB1]; omega_arith)]; exact hk.kb1 l hl
  · rw [w _ (by simp only [EK13]; omega_arith) (by simp only [EK13]; omega_arith)]; exact hk.k13 l hl
  · rw [w _ (by simp only [EK26]; omega_arith) (by simp only [EK26]; omega_arith)]; exact hk.k26 l hl
  · rw [w _ (by simp only [EK39]; omega_arith) (by simp only [EK39]; omega_arith)]; exact hk.k39 l hl

/-! ## Positions -/

/-- What a position in the lanes may change: `LKeep`'s, and the counter. -/
structure BKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  r11 : t.gpr .r11 = s.gpr .r11
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 56 1288 s.mem t.mem
  d : env t.mem base 16 = env s.mem base 16

theorem BKeep.refl (base : Addr) (s : State) : BKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, rfl⟩

theorem BKeep.trans {base : Addr} {s t u : State} (h : BKeep base s t) (k : BKeep base t u) :
    BKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.r11.trans h.r11, k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem, k.d.trans h.d⟩

theorem BKeep.of_lkeep {base : Addr} {s t : State} (h : LKeep base s t) : BKeep base s t :=
  ⟨h.gpr, h.r11, h.rd, h.wr, h.mem.mono (by decide) (by decide), h.slot 16⟩

theorem BKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ (r ∈ clob ∧ r ≠ .r11)) : BKeep base s t :=
  BKeep.of_lkeep (LKeep.of_keeps h hrs)

theorem BKeep.byte {base : Addr} {s t : State} (h : BKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem BKeep.consts {base : Addr} {s t : State} (h : BKeep base s t) (hk : EConsts s.mem base) :
    EConsts t.mem base := hk.below h.mem (by decide)

/-- `batchBegin`: the counter moved down, and what it keeps. -/
theorem vbatchBegin_ok {s : State} {base : Addr} (hs : Scratch s base) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block batchBegin) s fun t => t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
      BKeep base s t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi :=
  WP.mono (WP.vk (batchBegin_ok hs j hc)) fun _ ⟨⟨_, av, ag, ar, aw, am⟩, ax, ay⟩ =>
    ⟨av, ⟨fun r _ hb _ => ag r hb, ag _ (by decide), ar, aw, am.mono (by decide) (by decide),
      by rw [header_env am]⟩, ax, ay⟩

/-! ## The invariants in the lanes -/

/-- `WinAt`'s, with the point in the lanes (with `T`), its limbs small, and the constants. -/
structure VAt (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (v : EPoint dZ)
    (c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp T A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  digits : DigitsAre s.mem base fA fB
  value : Rep (lanePt s) v
  small : Small s
  consts : EConsts s.mem base
  keep : BKeep base s₀ s

theorem VAt.of_keep {s₀ s t : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {v v' : EPoint dZ} {c c' : Nat} (h : VAt s₀ base kp sp T A fA fB v c s) (k : BKeep base s t)
    (hc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 c') (hv : Rep (lanePt t) v') (hsm : Small t) :
    VAt s₀ base kp sp T A fA fB v' c' t :=
  ⟨h.ctx.of_byte k.byte, by rw [k.d]; exact h.d, hc, h.digits.of_byte k.byte.mem, hv, hsm,
    k.consts h.consts, h.keep.trans k⟩

theorem VAt.congr {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {v v' : EPoint dZ} {c : Nat} (h : VAt s₀ base kp sp T A fA fB v c s) (e : v = v') :
    VAt s₀ base kp sp T A fA fB v' c s := e ▸ h

/-- Scalar code keeping the counter, the lanes and what a position keeps. -/
theorem VAt.of_scalar {s₀ s t : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {v : EPoint dZ} {c : Nat} (h : VAt s₀ base kp sp T A fA fB v c s) {rs : List Reg} (k : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ (r ∈ clob ∧ r ≠ .r11)) (hx : t.xmm = s.xmm)
    (hy : t.ymmHi = s.ymmHi) : VAt s₀ base kp sp T A fA fB v c t :=
  have ⟨pt, st⟩ := lanePt_vec hx hy
  h.of_keep (BKeep.of_keeps k hrs) (by rw [k.2.1]; exact h.counter) (by rw [pt]; exact h.value) (st h.small)

/-- After position `p`. -/
abbrev VLoop (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top p : Nat)
    (s : State) : Prop :=
  VAt s₀ base kp sp T A fA fB (winVal A fA fB top p) p s

/-- Skipping, with the counter at `q`: the digits from `q` to `top` are zero. -/
structure VSkip (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top q : Nat)
    (s : State) : Prop where
  loop : VLoop s₀ base kp sp T A fA fB top q s
  zero : ∀ j, q ≤ j → j ≤ top → fA j = 0 ∧ fB j = 0
  pos : 0 < q
  le : q ≤ top + 1

/-! ## A position -/

/-- `k`'s digit at `p` added. -/
theorem vaddA_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {v : EPoint dZ}
    {top p : Nat} (hdg : Digits fA fB top) (hp : p ≤ top) (h : VAt s₀ base kp sp T A fA fB v p s) :
    WP isa (.seq (.block (digitAt 0)) (vaddDigit 5376)) s
      (VAt s₀ base kp sp T A fA fB (v + (Recode.dec (fA p)) • A) p) := by
  refine WP.seq (WP.mono (WP.vk (digitAt_ok h.ctx.scratch (by have := hdg.top; omega_arith) (by decide) h.counter))
    fun a ⟨⟨ab, az, ka⟩, ax, ay⟩ => ?_)
  rw [(h.digits p (by have := hdg.top; omega_arith)).1] at ab az
  have ha := h.of_scalar ka (by decide) ax ay
  refine WP.mono (vaddDigit_ok ha.ctx.scratch ha.consts ha.small (by decide) (by decide) ha.ctx.aTab (fA p)
    (hdg.a p) ab az ha.value) fun t ⟨tr, tsm, kt⟩ => ?_
  exact ha.of_keep (BKeep.of_lkeep kt) (kt.win.counter.trans ha.counter) tr tsm

/-- `S`'s digit at `p` added. -/
theorem vaddB_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {v : EPoint dZ}
    {top p : Nat} (hdg : Digits fA fB top) (hp : p ≤ top) (h : VAt s₀ base kp sp T A fA fB v p s) :
    WP isa (.seq (.block (digitAt 1)) vaddBase) s
      (VAt s₀ base kp sp T A fA fB (v + (Recode.dec (fB p)) • (-baseAff)) p) := by
  refine WP.seq (WP.mono (WP.vk (digitAt_ok h.ctx.scratch (by have := hdg.top; omega_arith) (by decide) h.counter))
    fun a ⟨⟨ab, az, ka⟩, ax, ay⟩ => ?_)
  rw [(h.digits p (by have := hdg.top; omega_arith)).2] at ab az
  have ha := h.of_scalar ka (by decide) ax ay
  refine WP.mono (vaddBase_ok ha.ctx.scratch ha.consts ha.small ha.ctx.bHeader ha.ctx.bTab (fB p) (hdg.b p)
    ab az ha.value) fun t ⟨tr, tsm, kt⟩ => ?_
  exact ha.of_keep (BKeep.of_lkeep kt) (kt.win.counter.trans ha.counter) tr tsm

/-- The digits at `p` added. -/
theorem vaddsAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {v : EPoint dZ}
    {top p : Nat} (hdg : Digits fA fB top) (hp : p ≤ top) (h : VAt s₀ base kp sp T A fA fB v p s) :
    WP isa vaddsAt s
      (VAt s₀ base kp sp T A fA fB (v + (Recode.dec (fA p)) • A + (Recode.dec (fB p)) • (-baseAff)) p) := by
  rw [vaddsAt]
  apply WP.assoc
  exact WP.seq (WP.mono (vaddA_ok hdg hp h) fun _ ha => vaddB_ok hdg hp ha)

/-- The doubling. -/
theorem vdblAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {v : EPoint dZ}
    {c : Nat} (h : VAt s₀ base kp sp T A fA fB v c s) :
    WP isa (.block vdbl) s (VAt s₀ base kp sp T A fA fB ((2 : Int) • v) c) := by
  refine WP.mono (vdbl_wp h.ctx.scratch.rdi (ctx_of h.ctx.scratch) h.consts h.small)
    fun b ⟨bg, brd, bwr, bo, bsm, bp⟩ => ?_
  have kb : LKeep base s b := ⟨fun r _ _ _ => by rw [bg], by rw [bg], brd, bwr, bo⟩
  exact h.of_keep (BKeep.of_lkeep kb) (kb.win.counter.trans h.counter)
    (by rw [bp, two_zsmul]; exact dblPoint_rep h.value.proj) bsm

/-- The position below: from after `p + 1` to after `p`, ZF set if `p` is zero. -/
theorem vstepAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : VLoop s₀ base kp sp T A fA fB top (p + 1) s) :
    WP isa vstepAt s fun t => t.zf = some (decide (p = 0)) ∧ VLoop s₀ base kp sp T A fA fB top p t := by
  rw [vstepAt]
  refine WP.seq (WP.mono (vbatchBegin_ok h.ctx.scratch p h.counter) fun a ⟨ac, ka, ax, ay⟩ => ?_)
  obtain ⟨pa, sa⟩ := lanePt_vec ax ay
  have ha : VAt s₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p a :=
    h.of_keep ka ac (by rw [pa]; exact h.value) (sa h.small)
  refine WP.seq (WP.mono (vdblAt_ok ha) fun b hb => ?_)
  refine WP.seq (WP.mono (vaddsAt_ok hdg hp hb) fun c hc => ?_)
  refine WP.mono (WP.vk (counterTest_ok hc.ctx.scratch (by have := hdg.top; omega_arith) hc.counter))
    fun t ⟨⟨tz, kt⟩, tx, ty⟩ => ⟨tz, (hc.of_scalar kt (by decide) tx ty).congr ?_⟩
  rw [winVal_step A fA fB hp]

/-! ## Skipping the leading zero digits -/

/-- A step of the skipping, below `p + 1`, as `skipTop_ok`. -/
theorem vskipTop_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (h : VSkip s₀ base kp sp T A fA fB top (p + 1) s) :
    WP isa skipTop s fun t => t.zf = some (skipStops fA fB p) ∧
      (skipStops fA fB p = true → VAt s₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p t) ∧
      (skipStops fA fB p = false → VSkip s₀ base kp sp T A fA fB top p t) := by
  have hle := h.le
  have hl := h.loop
  have h0 : winVal A fA fB top (p + 1) = 0 := winVal_zero h.zero
  rw [skipTop]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (vbatchBegin_ok hl.ctx.scratch p hl.counter) fun a ⟨ac, ka, ax, ay⟩ => ?_
  obtain ⟨pa, sa⟩ := lanePt_vec ax ay
  have ha : VAt s₀ base kp sp T A fA fB 0 p a :=
    hl.of_keep ka ac (by rw [pa, ← h0]; exact hl.value) (sa hl.small)
  refine WP.mono (WP.vk (digitsAt_ok ha.ctx.scratch (by have := hdg.top; omega_arith) ha.counter))
    fun b ⟨⟨bz, kb⟩, bx, bw⟩ => ?_
  rw [(ha.digits p (by have := hdg.top; omega_arith)).1, (ha.digits p (by have := hdg.top; omega_arith)).2] at bz
  have hb := ha.of_scalar kb (by decide) bx bw
  have e2 : (0 : EPoint dZ) = (2 : Int) • winVal A fA fB top (p + 1) := by rw [h0, smul_zero]
  refine WP.ite (!decide (fA p = 0 ∧ fB p = 0)) (by simp only [eval, bz, Option.map_some])
    (fun hz => ?_) (fun hz => ?_)
  · have hst : skipStops fA fB p = true := by
      simp only [skipStops, hz, Bool.true_or]
    refine WP.mono (WP.vk (cmpSelf_ok b)) fun t ⟨⟨tz, kt⟩, tx, ty⟩ => ⟨by rw [tz, hst],
      fun _ => (hb.of_scalar kt (by decide) tx ty).congr e2, fun hf => absurd hf (by rw [hst]; decide)⟩
  · have hz0 : fA p = 0 ∧ fB p = 0 := by simpa using hz
    refine WP.mono (WP.vk (counterTest_ok hb.ctx.scratch (by have := hdg.top; omega_arith) hb.counter))
      fun t ⟨⟨tz, kt⟩, tx, ty⟩ => ?_
    have ht := hb.of_scalar kt (by decide) tx ty
    have hst : skipStops fA fB p = decide (p = 0) := by
      simp only [skipStops, hz0, and_self, decide_true, Bool.not_true, Bool.false_or]
    by_cases hp0 : p = 0
    · subst hp0
      exact ⟨by rw [tz, hst], fun _ => ht.congr e2, fun hf => absurd hf (by rw [hst]; decide)⟩
    · have hz' : ∀ j, p ≤ j → j ≤ top → fA j = 0 ∧ fB j = 0 := fun j h1 h2 => by
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
        · exact hz0
        · exact h.zero j (by omega_arith) h2
      exact ⟨by rw [tz, hst], fun hs => absurd hs (by rw [hst]; simp [hp0]),
        fun _ => ⟨ht.congr (winVal_zero hz').symm, hz', by omega_arith, by omega_arith⟩⟩

/-- The windows in the lanes, from one above `top` to after position 0, `vstore` aside. -/
theorem vloops_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top : Nat}
    (hdg : Digits fA fB top) (h : VSkip s₀ base kp sp T A fA fB top (top + 1) s) {Q : State → Prop}
    (hq : ∀ t, VLoop s₀ base kp sp T A fA fB top 0 t → WP isa (.block vstore) t Q) :
    WP isa (.seq (.loop skipTop .ne) (.seq vaddsAt (.seq (.block batchTest)
      (.seq (.ite .ne (.loop vstepAt .ne) (.block [])) (.block vstore))))) s Q := by
  refine WP.seq (WP.mono (show WP isa (.loop skipTop .ne) s fun t =>
      ∃ p, p ≤ top ∧ VAt s₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p t by
    apply WP.loop (fun q t => VSkip s₀ base kp sp T A fA fB top q t) (n := top + 1)
    · intro q t ht
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.pos; omega_arith : q ≠ 0)
      have hle := ht.le
      refine WP.mono (vskipTop_ok hdg ht) fun u ⟨uz, ut, uf⟩ => ?_
      cases hs : skipStops fA fB p
      · exact Or.inr ⟨by simp only [eval, uz, hs, Option.map_some, Bool.not_false], p, by omega_arith, uf hs⟩
      · exact Or.inl ⟨by simp only [eval, uz, hs, Option.map_some, Bool.not_true], p, by omega_arith, ut hs⟩
    · exact h) fun a ⟨p, hp, ha⟩ => ?_)
  refine WP.seq (WP.mono (vaddsAt_ok hdg hp ha) fun b hb => ?_)
  have hb' : VLoop s₀ base kp sp T A fA fB top p b := hb.congr (by rw [winVal_step A fA fB hp])
  refine WP.seq (WP.mono (WP.vk (counterTest_ok hb'.ctx.scratch (by have := hdg.top; omega_arith) hb'.counter))
    fun c ⟨⟨cz, kc⟩, cx, cy⟩ => ?_)
  have hc := hb'.of_scalar kc (by decide) cx cy
  refine WP.seq ?_
  refine WP.ite (!decide (p = 0)) (by simp only [eval, cz, Option.map_some]) (fun hz => ?_) (fun hz => ?_)
  · have hp0 : p ≠ 0 := by simpa using hz
    refine WP.mono (show WP isa (.loop vstepAt .ne) c (VLoop s₀ base kp sp T A fA fB top 0) by
      apply WP.loop (fun n t => VLoop s₀ base kp sp T A fA fB top n t ∧ 0 < n ∧ n ≤ top) (n := p)
      · intro n t ⟨ht, hn0, hn⟩
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega_arith : n ≠ 0)
        refine WP.mono (vstepAt_ok hdg (by omega_arith) ht) fun u ⟨uz, hu⟩ => ?_
        by_cases hm : m = 0
        · subst hm
          exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
        · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hm, Option.map_some, Bool.not_false],
            m, by omega_arith, hu, by omega_arith, by omega_arith⟩
      · exact ⟨hc, by omega_arith, hp⟩) hq
  · have hp0 : p = 0 := by simpa using hz
    subst hp0
    exact WP.block_nil (hq c hc)

/-! ## Into the lanes and back -/

/-- Before the windows: the constants, and slots 0–3 in the lanes. -/
theorem wprep_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload)) s fun t =>
      (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 1664 224 s.mem t.mem ∧ EConsts t.mem base ∧ Small t ∧
      lanePt t = point (env s.mem base) 0 1 2 3 := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.consts_wp s)
    fun s₁ ⟨ha, hc, hd, hb, h8, h9, h10, _, _, g₁, m₁, rd₁, wr₁, _, _, _⟩ => ?_
  have hs₁ : Scratch s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.mono (vload_wp hs₁.rdi (ctx_of hs₁) ha hc hd hb h8 h9 h10) fun t ⟨g₂, rd₂, wr₂, o₂, k₂, u₂⟩ => ?_
  refine ⟨fun r hr => by rw [g₂, g₁ r (fun h => hr (cregs_clob r h))], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    by rw [← m₁]; exact o₂, k₂, fun l hl i hi => by have := (u₂ l hl i hi).2; omega_arith, ?_⟩
  have e : ∀ l (hl : l < 4), fe5 (lanes t 0 l) = env s.mem base ⟨l, by omega_arith⟩ := fun l hl => by
    rw [fe5_congr (fun i hi => (u₂ l hl i hi).1), fe5_load, m₁]; rfl
  simp only [lanePt, point]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
  rfl

/-- A run in the lanes, from `s₃`, entered from a run started in `s₀` satisfying `R₀`: what has
been kept since `s₀`, and `Q s₃`. -/
def VRun (R₀ : State → Prop) (base : Addr) (Q : State → State → Prop) (x : State) : Prop :=
  ∃ s₀ s₃, R₀ s₀ ∧ ByteKeep base s₀ s₃ ∧ Q s₃ x

/-- Into the lanes: the skipping's start. -/
theorem enter_ok {R₀ : State → Prop} {s : State} {base kp sp T : Addr} {A : EPoint dZ}
    {fA fB : Nat → Nat} {top : Nat} (h : StartRun R₀ base kp sp T A fA fB top s) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload)) s
      (VRun R₀ base fun s₃ => VSkip s₃ base kp sp T A fA fB top (top + 1)) := by
  obtain ⟨s₀, r₀, hk⟩ := h
  have h := hk.loop
  have hs := h.ctx.scratch
  refine WP.mono (wprep_ok hs) fun s₁ ⟨g₁, rd₁, wr₁, o₁, k₁, sm₁, p₁⟩ => ?_
  have m₁ : Outside base 56 1832 s.mem s₁.mem := o₁.mono (by decide) (by decide)
  have k₀₁ : ByteKeep base s s₁ := ⟨fun r hc _ _ => by rw [g₁ r hc], by rw [rd₁], by rw [wr₁], m₁⟩
  have m₁' : Outside base 1600 288 s.mem s₁.mem := o₁.mono (by decide) (by decide)
  refine ⟨s₀, s₁, r₀, h.keep.trans k₀₁, ?_⟩
  refine ⟨⟨h.ctx.of_byte k₀₁, ?_, ?_, h.digits.of_byte k₀₁.mem, ?_, sm₁, k₁, BKeep.refl _ _⟩, hk.zero,
    hk.pos, hk.le⟩
  · rw [show env s₁.mem base 16 = env s.mem base 16 from
      Outside_F m₁' (by simp only [offset]; omega_arith) (Or.inl (by simp only [offset]; omega_arith))]
    exact h.d
  · exact (m₁'.word (Or.inl (by decide)) (by decide)).trans h.counter
  · rw [p₁, winVal_zero hk.zero]; exact hk.full

/-- Back into slots 0–3. -/
theorem exit_ok {R₀ : State → Prop} {w : State} {base kp sp T : Addr} {A : EPoint dZ}
    {fA fB : Nat → Nat} {top : Nat}
    (h : VRun R₀ base (fun s₃ => VLoop s₃ base kp sp T A fA fB top 0) w) :
    WP isa (.block vstore) w (LoopRun R₀ base kp sp T A fA fB top 0) := by
  obtain ⟨s₀, s₃, r₀, k₀₃, hw⟩ := h
  have hsw : Scratch w base := hw.ctx.scratch
  refine WP.mono (vstore_wp hsw.rdi (ctx_of hsw) hw.consts hw.small) fun t ⟨tg, trd, twr, tou, tf⟩ => ?_
  have pt : point (env t.mem base) 0 1 2 3 = lanePt w := by
    simp only [point, lanePt, env, VG.Impl.Ed25519.X86_64.offset]
    rw [← tf 0 (by decide), ← tf 1 (by decide), ← tf 2 (by decide), ← tf 3 (by decide)]
    rfl
  have mwt : Outside base 64 1544 w.mem t.mem := tou.mono (by decide) (by decide)
  have kwt : ByteKeep base w t := ⟨fun r _ _ _ => by rw [tg], by rw [trd], by rw [twr],
    mwt.mono (by decide) (by decide)⟩
  have kst : ByteKeep base s₃ t := hw.keep.byte.trans kwt
  refine ⟨s₀, r₀, hw.ctx.of_byte kwt, ?_, ?_, hw.digits.of_byte kwt.mem, by rw [pt]; exact hw.value.proj,
    k₀₃.trans kst⟩
  · rw [show env t.mem base 16 = env w.mem base 16 from
        Outside_F tou (by simp only [offset]; omega_arith) (Or.inr (by simp only [offset]; omega_arith))]
    exact hw.d
  · exact (mwt.word (Or.inl (by decide)) (by decide)).trans hw.counter

/-- `Ifma.windows` keeps the windows' invariant, from one above `top` to after position 0. -/
theorem windows_ok {R₀ : State → Prop} {s : State} {base kp sp T : Addr} {A : EPoint dZ}
    {fA fB : Nat → Nat} {top : Nat} (hdg : Digits fA fB top) (h : StartRun R₀ base kp sp T A fA fB top s) :
    WP isa Impl.Ed25519.X86_64.Ifma.windows s (LoopRun R₀ base kp sp T A fA fB top 0) := by
  rw [Impl.Ed25519.X86_64.Ifma.windows]
  refine WP.seq (WP.mono (enter_ok h) fun s₃ h₃ => ?_)
  obtain ⟨s₀, s₃', r₀, k₀, v₃⟩ := h₃
  exact vloops_ok hdg v₃ fun w hw => exit_ok ⟨s₀, s₃', r₀, k₀, hw⟩

end VG.Proof.Ed25519.X86_64.Ifma
