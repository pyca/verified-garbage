module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcMain
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
-- separate module: the precompute's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # FFDH's context on RISC-V: with p valid

`bound_step` and `rest_ok`: from p checked and the recognized width in
`a5` (`MP`), the bound's bit length, the width and the metadata,
`R² mod p`, the prefix rows and the table: the context's words are
`generationValues`. -/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Precompute
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Spec.RsaKeyGen (bitLength)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (A WCtx slot24 slot_lt)

/-- At `main`: the exchange's state with p valid in array 0, the domain's
registers, the recognized width in `a5`, the domain valid, and the context
writable and apart. -/
structure MP (x : XD) (s : State) : Prop where
  base : Base x s
  hp : wordsVal s.mem x.S (slot x.w 0) x.w = x.p
  a2 : s.gpr .a2 = x.D
  a3 : s.gpr .a3 = BitVec.ofNat 64 x.L
  a4 : s.gpr .a4 = BitVec.ofNat 64 x.k
  a5 : s.gpr .a5 = BitVec.ofNat 64 (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups x.k x.db)
  dv : Spec.Ffdh.domainValid x.k x.db = true
  hL : x.L = 2 * x.k ∨ x.L = 3 * x.k
  hY : x.Y = off x.D x.k
  hc : Scr s x.O (8 * ctxWords x.w)
  sepCB : ∀ y, ofs x.O y < 8 * ctxWords x.w → x.Z ≤ ofs x.S y
  sepBC : ∀ y, ofs x.S y < x.Z → 8 * ctxWords x.w ≤ ofs x.O y
  sepDC : ∀ i < x.L, ∀ y, ofs x.O y < 8 * ctxWords x.w → off x.D i ≠ y

/-- The bound's bit length. -/
abbrev blOf (x : XD) : Nat := bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf x.k x.db))

theorem scr_shrink {s : State} {b : Addr} {n m : Nat} (hs : Scr s b n) (h : m ≤ n) : Scr s b m :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, hm, hb, by omega_arith, hL'⟩,
    by have := hs.nowrap; omega_arith, hs.al⟩

theorem MP.keep {x : XD} {s t : State} {rs : List Reg} (h : MP x s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ baseRegs ++ ([.a2, .a3, .a4, .a5] : List Reg), r ∉ rs) : MP x t :=
  ⟨h.base.same k hm (fun r hr' => hr r (List.mem_append_left _ hr')), by rw [hm]; exact h.hp,
    (k.gpr (hr _ (by decide))).trans h.a2, (k.gpr (hr _ (by decide))).trans h.a3,
    (k.gpr (hr _ (by decide))).trans h.a4, (k.gpr (hr _ (by decide))).trans h.a5, h.dv, h.hL, h.hY,
    h.hc.congr k.2.2, h.sepCB, h.sepBC, h.sepDC⟩

/-- The bound's bit length is at most p's. -/
theorem bl_le {k : Nat} {dom : List Byte} (hv : Spec.Ffdh.domainValid k dom = true) :
    bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) ≤ 8 * k := by
  have hv' := (VG.Proof.Ffdh.domainValid_iff k dom).mp hv
  have hle : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≤ (Spec.Ffdh.domainOf k dom).p := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega_arith
    | some q => have := (hv'.2.2 q hq).1.2.2; simp only [Option.getD_some]; omega_arith
  have hp : (Spec.Ffdh.domainOf k dom).p < 2 ^ (8 * k) := by
    have h1 := VG.Proof.Bignum.os2ip_lt (dom.take k)
    have h2 : 256 ^ (dom.take k).length ≤ 2 ^ (8 * k) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega_arith)
    change Spec.Rsa.os2ip (dom.take k) < _
    omega_arith
  exact VG.Proof.Ffdh.ContextRows.bitLength_le_of_lt (Nat.lt_of_le_of_lt hle hp)

/-- `bound`: the bound's bit length into `s3`. -/
theorem bound_step {x : XD} {s : State} (h : MP x s) :
    WP isa bound s fun t => (MP x t ∧ t.gpr .s3 = BitVec.ofNat 64 (blOf x)) ∧ t.mem = s.mem := by
  have hb := h.base
  have hc := hb.ctx
  have hk := hc.k64; have hk' := hc.k1024
  have hf := VG.Proof.Bignum.valid_facts ((VG.Proof.Ffdh.domainValid_iff _ _).mp h.dv).1 hk
  have hlen : (Spec.Rsa.bytesAt s.mem x.D x.L).length = x.L := by simp [Spec.Rsa.bytesAt]
  have hp : ∀ m : Mem, Spec.Rsa.bytesAt m x.D x.L = x.db →
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.D x.k) = (Spec.Ffdh.domainOf x.k x.db).p := fun m e => by
    rw [← e, Proof.Ffdh.domainOf_p _ _ (by rcases h.hL with e' | e' <;> omega_arith)]
  refine WP.mono (bound_ok h.a2 h.a3 h.a4 h.hL (by omega_arith) hk' hc.rdD (fun _ => by
      rw [hp _ hc.bD]; exact ⟨hf.1, hf.2.1⟩)
    (by rw [hc.bD]; exact lead_ne (by omega_arith) (by rw [← hc.bD, hlen]; exact h.hL) h.dv))
    fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨h.keep kt tm (by decide), by rw [t3, hc.bD]⟩, tm⟩

/-- `TS` with the memory it keeps below array 1 from now on. -/
theorem TS.remem {s : State} {B C : Addr} {Z w P : Nat} {M : Mem} (h : TS s B C Z w P M) : TS s B C Z w P s.mem :=
  ⟨h.win, h.h10, h.hc, h.sepCB, h.sepBC, h.odd, h.one, fun _ _ => rfl⟩

theorem CtxKeep.out {C : Addr} {w : Nat} {m m' : Mem} (h : CtxKeep C w m m') : Outside C (rowOff w 2) (2 ^ 64) m m' :=
  fun y hy => hy.elim (h y) fun h' => absurd h' (by have := (y - C).isLt; simp only [ofs]; omega_arith)

/-- After `bound`: the width, the metadata, `R² mod p`, the prefix and the
table. -/
theorem rest_ok {x : XD} {s : State} (h : MP x s) (h3 : s.gpr .s3 = BitVec.ofNat 64 (blOf x)) :
    WP isa (.seq width (.seq (.block metadata) (.seq VG.Impl.Ffdh.RISCV64.r2 (.seq storePrefix (.seq table (.block [.li .a0 1]))))))
      s fun t =>
      Spec.Rsa.wordsAt t.mem x.O (3 + 34 * x.w) = VG.Proof.Ffdh.generationValues x.k x.db ∧ t.gpr .a0 = 1 ∧
        t.gpr .s6 = x.S ∧ (∀ y, ofs x.S y < 256 → t.mem y = s.mem y) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hb := h.base
  have hc := hb.ctx
  have hk := hc.k64; have hk' := hc.k1024
  have hZ := hc.hZ; have hn := hc.scr.nowrap
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have hw8 : 8 ≤ x.w := by omega_arith
  have hw' : x.w < 2 ^ 31 := by omega_arith
  have hv' := (VG.Proof.Ffdh.domainValid_iff _ _).mp h.dv
  have hf := VG.Proof.Bignum.valid_facts hv'.1 hk
  have hpx : x.p = (Spec.Ffdh.domainOf x.k x.db).p := rfl
  have hlen : x.db.length = x.L := by rw [← hc.bD]; simp [Spec.Rsa.bytesAt]
  have hd : x.db.length = 2 * x.k ∨ x.db.length = 3 * x.k := by rw [hlen]; exact h.hL
  have e24 : slot x.w 24 = 256 + 24 * (8 * (x.w + 2)) := by simp [slot, hdrBytes]
  have e0 : slot x.w 0 = 256 := by simp [slot, hdrBytes]
  have e1 : slot x.w 1 = 256 + 8 * (x.w + 2) := by simp [slot, hdrBytes]
  have e8 : slot x.w 8 = 256 + 8 * (8 * (x.w + 2)) := by simp [slot, hdrBytes]
  have hCn := h.hc.nowrap
  -- The width.
  have hcap := recognize_lt (by omega_arith) hd hf.2.2
  have hbl : blOf x ≤ 8 * x.k := bl_le h.dv
  refine WP.seq (WP.mono (width_ok h.a5 h3 (by omega_arith) (by omega_arith)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ => ?_)
  rw [width_eq (by omega_arith) hd hf.2.2] at a9
  have hgb := VG.Proof.Ffdh.ContextRows.genBits_facts h.dv
  generalize hbits : Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf x.k x.db) = bits at a9 hgb
  -- The metadata.
  have h10 : s₁.gpr .s10 = x.O := (k1.gpr (by decide)).trans (hb.s10.trans (add_ofNat_zero _))
  refine WP.seq (WP.mono (metadata_ok (scr_shrink (h.hc.congr k1.2.2) (by unfold ctxWords; omega_arith)) h10 a9
    (by omega_arith)) fun s₂ ⟨⟨c0, c8, c16, a9', o2⟩, k2⟩ => ?_)
  rw [m1] at o2
  have k12 := k1.trans k2
  have o2S : Outside x.S x.Z (2 ^ 64) s.mem s₂.mem := ctx_of_scr o2 (by unfold ctxWords; omega_arith) h.sepBC
  -- `R² mod p`.
  unfold VG.Impl.Ffdh.RISCV64.r2
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k12.gpr (by decide)).trans hb.a7)
    ((k12.gpr (by decide)).trans hb.s5) 1) fun s₃ ⟨⟨b2, m3⟩, k3⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k12.trans k3).gpr (by decide) |>.trans hb.a7)
    ((k12.trans k3).gpr (by decide) |>.trans hb.s5) 2) fun s₄ ⟨⟨b5, m4⟩, k4⟩ => ?_
  have k14 := (k12.trans k3).trans k4
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) (k14.gpr (by decide) |>.trans hb.a7)
    (k14.gpr (by decide) |>.trans hb.s5) 3) fun s₅ ⟨⟨b6, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  have hm5 : s₅.mem = s₂.mem := by rw [m5, m4, m3]
  have p5 : wordsVal s₅.mem x.S (slot x.w 0) x.w = x.p := by
    rw [hm5, Outside.wordsVal o2S (Or.inl (by omega_arith)) (by omega_arith)]; exact h.hp
  refine WP.mono (r2t_ok (hc.scr.congr k15.2.2) ((k4.trans k5).gpr (by decide) |>.trans b2)
    ((k5.gpr (by decide)).trans b5) b6 (k15.gpr (by decide) |>.trans hb.a7) (k15.gpr (by decide) |>.trans hb.t0)
    (by omega_arith) hw' (by omega_arith) (by rw [p5]; exact hf.2.2) (by rw [p5]; exact hf.1))
    fun s₆ ⟨⟨rr6, inv6, o6⟩, k6⟩ => ?_
  rw [p5] at rr6
  have k16 := k15.trans k6
  have o6C : Outside x.O (8 * ctxWords x.w) (2 ^ 64) s₅.mem s₆.mem :=
    ctx_of_scr o6 (by omega_arith) h.sepCB
  have hlow6 : ∀ y, ofs x.S y < slot x.w 1 → s₆.mem y = s₅.mem y := fun y hy => o6 y (Or.inl hy)
  have hw06 : Mont.word s₆.mem x.S (slot x.w 0) = Mont.word s₅.mem x.S (slot x.w 0) :=
    Outside.word o6 (Or.inl (by omega_arith)) (by omega_arith)
  have p6 : wordsVal s₆.mem x.S (slot x.w 0) x.w = x.p := by
    rw [Outside.wordsVal o6 (Or.inl (by omega_arith)) (by omega_arith)]; exact p5
  have ts6 : TS s₆ x.S x.O x.Z x.w x.p s₆.mem :=
    ⟨⟨hc.scr.congr (k16.2.2), by omega_arith, hw', hZ, k6.gpr (by decide) |>.trans (k15.gpr (by decide) |>.trans hb.a7),
      k16.gpr (by decide) |>.trans hb.s5, k16.gpr (by decide) |>.trans hb.t0, by rw [hw06]; exact inv6, p6⟩,
      (k16.gpr (by decide)).trans (hb.s10.trans (add_ofNat_zero _)), h.hc.congr k16.2.2, h.sepCB, h.sepBC, hf.1, hf.2.1,
      fun _ _ => rfl⟩
  -- The prefix.
  refine WP.seq (WP.mono (storePrefix_ok ts6) fun s₇ ⟨⟨r0, r1, o7, b7, ts7⟩, k7⟩ => ?_)
  have k17 := k16.trans k7
  -- The table.
  have hg : ∀ m : Mem, Spec.Rsa.bytesAt m x.D x.L = x.db →
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off x.D x.k) x.k) = (Spec.Ffdh.domainOf x.k x.db).g := fun m e => by
    rw [← e, Proof.Ffdh.domainOf_g _ _ (by rcases h.hL with e' | e' <;> omega_arith)]
  have hsepC : ∀ i < x.k, ∀ y, ofs x.O y < 8 * ctxWords x.w → off (off x.D x.k) i ≠ y := fun i hi y hy => by
    rw [Derive.off_off]; exact h.sepDC (x.k + i) (by rcases h.hL with e' | e' <;> omega_arith) y hy
  have hsepS : ∀ i < x.k, ∀ y, ofs x.S y < x.Z → off (off x.D x.k) i ≠ y := fun i hi y hy => by
    rw [← h.hY]; exact hc.sepY i hi y hy
  have hb7 : Spec.Rsa.bytesAt s₇.mem (off x.D x.k) x.k = Spec.Rsa.bytesAt s.mem (off x.D x.k) x.k := by
    rw [Pub.bytes_apart (Z := 8 * ctxWords x.w) o7 (by unfold rowOff ctxWords; omega_arith) hsepC,
      Pub.bytes_apart (Z := x.Z) o6 (by omega_arith) hsepS, hm5,
      Pub.bytes_apart (Z := 8 * ctxWords x.w) o2 (by unfold ctxWords; omega_arith) hsepC]
  have h9 : s₇.gpr .s9 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) :=
    ((k3.trans k4).trans k5 |>.trans k6 |>.trans k7).gpr (by decide) |>.trans a9'
  have hrows := VG.Proof.Rsa.FixedBaseComb.rows_small (show bits ≤ 8192 by omega_arith)
  have hrpos := VG.Proof.Rsa.FixedBaseComb.rows_pos (show 0 < bits by omega_arith)
  have hgp : (Spec.Ffdh.domainOf x.k x.db).g < x.p := by have := hv'.2.1; omega_arith
  have a17 : A s₇.mem x.S x.w 1 = 2 ^ (64 * x.w) * 2 ^ (64 * x.w) % x.p := by
    show wordsVal s₇.mem x.S (slot x.w 1) x.w = _
    rw [Outside.wordsVal b7 (Or.inl (by omega_arith)) (by omega_arith), rr6, ← Nat.pow_add]
    congr 2; omega_arith
  refine WP.seq (WP.mono (table_ok (D := x.D) (k := x.k) (G := (Spec.Ffdh.domainOf x.k x.db).g) (bits := bits)
    ⟨ts7.remem, h9, CtxKeep.of_eq rfl, Keep.refl _ _⟩ hrpos (by omega_arith) a17
    (k17.gpr (by decide) |>.trans hb.s6) (k17.gpr (by decide) |>.trans hb.s7) (k17.gpr (by decide) |>.trans hb.s11)
    (by omega_arith) (by omega_arith) (fun i hi => by rw [k17.2.1, k17.2.2, ← h.hY]; exact hc.rdY i hi) hsepS hsepC
    (by rw [hb7]; exact hg _ hc.bD) hgp) fun s₈ ⟨tt8, e8'⟩ => ?_)
  -- `a0 := 1`.
  refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = 1 ∧ t.mem = s₈.mem) (by brun [Pub.pub_li1]; rfl)
    (by rfl) (by rfl)) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have k8 := tt8.kr
  have ck := tt8.keep.out
  have hrow2 : rowOff x.w 1 + 8 * x.w ≤ rowOff x.w 2 := by unfold rowOff; omega_arith
  have hrow02 : rowOff x.w 0 + 8 * x.w ≤ rowOff x.w 2 := by unfold rowOff; rw [Nat.mul_zero]; omega_arith
  have hcw : 8 * ctxWords x.w = 24 + 272 * x.w := by unfold ctxWords; omega_arith
  have hr2 : rowOff x.w 2 = 24 + 16 * x.w := by unfold rowOff; omega_arith
  have wd : ∀ d, d + 8 ≤ 24 → word t.mem x.O d = word s₂.mem x.O d := fun d hd => by
    rw [mt, Outside.word ck (Or.inl (by unfold rowOff; omega_arith)) (by omega_arith),
      Outside.word o7 (Or.inl (by unfold rowOff; omega_arith)) (by omega_arith),
      Outside.word o6C (Or.inl (by unfold ctxWords; omega_arith)) (by omega_arith), hm5]
  refine ⟨?_, t0, (kt.gpr (by decide)).trans (k8.gpr (by decide) |>.trans (k17.gpr (by decide) |>.trans hb.s6)),
    fun y hy => ?_, by rw [kt.2.1, k8.2.1, k17.2.1], by rw [kt.2.2, k8.2.2, k17.2.2]⟩
  · have c0' : word t.mem x.O 0 = BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf x.k x.db)) := by
      rw [wd 0 (by decide), c0, hbits]
    have c8' : word t.mem x.O 8 =
        BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf x.k x.db) + 7) / 8) := by
      rw [wd 8 (by decide), c8, hbits]
    have c16' : word t.mem x.O 16 = BitVec.ofNat 64
        (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf x.k x.db))) := by
      rw [wd 16 (by decide), c16, hbits]
    have hp' : wordsVal t.mem x.O (rowOff x.w 0) x.w = (Spec.Ffdh.domainOf x.k x.db).p := by
      rw [mt, Outside.wordsVal ck (Or.inl hrow02) (by unfold rowOff; rw [Nat.mul_zero]; omega_arith), r0]
      exact ts6.win.n
    have hr' : wordsVal t.mem x.O (rowOff x.w 1) x.w =
        2 ^ (64 * x.w) * 2 ^ (64 * x.w) % (Spec.Ffdh.domainOf x.k x.db).p := by
      rw [mt, Outside.wordsVal ck (Or.inl hrow2) (by unfold rowOff; omega_arith), r1]
      show wordsVal s₆.mem x.S (slot x.w 1) x.w = _
      rw [rr6, ← Nat.pow_add]
      congr 2; omega_arith
    have he' : Ents t.mem x.O (Spec.Ffdh.domainOf x.k x.db).g (Spec.Ffdh.domainOf x.k x.db).p x.w
        (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf x.k x.db)) 32 := by
      rw [hbits]; intro a ha; rw [ent, mt]; exact e8' a ha
    exact ctx_words (k := x.k) (dom := x.db) c0' c8' c16' hp' hr' he'
  · have hy' : ofs x.S y < x.Z := by omega_arith
    rw [mt, tt8.ts.low y (by omega_arith), b7 y (Or.inl hy'), o6 y (Or.inl (by omega_arith)), hm5,
      o2 y (Or.inr (by have := h.sepBC y hy'; omega_arith))]

end VG.Proof.Ffdh.RISCV64.Cached
