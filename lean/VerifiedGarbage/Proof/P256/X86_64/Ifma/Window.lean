module

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.VLoop
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Ends
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointTables
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoopTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMul
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-!
# P-256 on x86-64 with AVX512_IFMA: the joint multiplication with the loop in vectors

`vloop_ok`: the loop over the digits leaves the rows of the sum's triple in the slots, or nothing if
every digit was zero. `vwindow_ok`: `R` is `[u]G + [v]Q`, by the loop in vectors or, where that leaves `Z`
zero, by `Joint.window`, which the loop in vectors leaves the input of (`VFin`).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open Spec.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Bignum.X86_64.Ifma (qv qv_setVy)
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)
open VG.Impl.Mont.X86_64 (sc csubC)
open VG.Impl.Mont (Mod)

/-! ### The loop's start -/

/-- Registers `0` to `n - 1` zeroed. -/
theorem zero_ok : ∀ (n : Nat) (s : State),
    WP isa (.block ((List.range n).map fun r => Instr.eop (.bin .vpxorq (vreg r) (vreg r) (vreg r)))) s fun t =>
      (∀ r, r < n → ∀ k, k < 4 → qv t (vreg r) k = 0) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr
  | 0, s => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩
  | n + 1, s => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zero_ok n s) fun a ⟨hz, hg, hm, hrd, hwr⟩ => ?_
    refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ⟨fun r hr k hk => ?_, ?_, ?_, ?_, ?_⟩⟩
    · show qv (a.setVy (vreg n) _) (vreg r) k = 0
      rw [qv_setVy]
      split
      · rw [VG.Proof.Bignum.X86_64.Ifma.qword256_lanes _ _ _ hk]
        simp [EBinOp.sse, XBinOp.eval, VG.X86_64.qword]
      · rename_i hne
        exact hz r (by rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | h; exact h; exact absurd (h ▸ rfl) hne) k hk
    · rw [← hg]; funext r; exact VG.Proof.Bignum.X86_64.Ifma.gpr_setVy a _ _ r
    · rw [← hm]; show (a.setVy (vreg n) _).mem = a.mem; cases vreg n <;> rfl
    · rw [← hrd]; show (a.setVy (vreg n) _).rd = a.rd; cases vreg n <;> rfl
    · rw [← hwr]; show (a.setVy (vreg n) _).wr = a.wr; cases vreg n <;> rfl

theorem kwords_eq : kwords = par.cst.map (BitVec.ofNat 64) := by decide +kernel

theorem kwords_length : kwords.length = 220 := by decide +kernel

/-- The blocks' constants in the working space are apart from the vectors' slots. -/
theorem sep_pool {base : Addr} {d : Nat} (hd : d + 32 ≤ 1760) :
    Mem.Sep (base + BitVec.ofNat 64 KB + BitVec.ofNat 64 d) 32 (base + BitVec.ofNat 64 par.lo) (par.win - par.lo) := by
  intro x hx hy
  have hlo : par.lo = 5056 := rfl
  have hwin : par.win = 5920 := rfl
  rw [Offset.add_add, Offset.lt_iff x base (by simp only [KB]; omega)] at hx
  rw [Offset.lt_iff x base (by omega)] at hy
  simp only [KB] at hx
  omega

/-- The words `ws` written to `o` of the working space. -/
theorem fill_ok {size : Nat} : ∀ (ws : List (BitVec 64)) {s : State} {base : Addr} {o : Nat},
    Scr s base size → o + 8 * ws.length ≤ size →
    WP isa (.block (fill ws o)) s fun t =>
      (∀ i, i < ws.length → word t.mem base (o + 8 * i) = ws.getD i 0) ∧ KeepRegs [.rax] s t ∧
        Outside base o (8 * ws.length) s.mem t.mem
  | [], s, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | w :: ws, s, base, o, hs, ho => by
    have hn := hs.nowrap
    simp only [List.length_cons] at ho
    show WP isa (.block ([.movImm64 .rax w] ++ ([.store (sc o) .rax] ++ fill ws (o + 8)))) s _
    rw [WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.movImm64 .rax w]) s
        (fun a => a.gpr .rax = w ∧ VG.Proof.X25519.X86_64.Keeps [.rax] s a) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg, ite_true, Option.some.injEq,
        exists_eq_left']
      refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun a ⟨ha, ka⟩ => ?_
    have hsa := hs.of_keeps ka (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (stores_ok [.rax] hsa (o := o) (by simp only [List.length]; omega) (by decide))
      fun b ⟨eb, kb, Ob⟩ => ?_
    have hsb := hsa.of_keepRegs kb (by simp)
    have wb : word b.mem base o = w := by
      apply BitVec.eq_of_toNat_eq
      have := eb
      simp only [List.length, wordsVal, regsVal, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
      rw [this, ha]
    refine WP.mono (fill_ok ws hsb (o := o + 8) (by omega)) fun t ⟨et, kt, Ot⟩ => ?_
    refine ⟨fun i hi => ?_, ⟨fun r hr => (kt.gpr r hr).trans ((kb.gpr r List.not_mem_nil).trans (ka.1 r hr)),
      kt.rd.trans (kb.rd.trans ka.2.2.1), kt.wr.trans (kb.wr.trans ka.2.2.2)⟩, fun x hx => ?_⟩
    · cases i with
      | zero =>
        rw [Nat.mul_zero, Nat.add_zero, Ot.word (by omega) (by omega), wb]
        rfl
      | succ i =>
        simp only [List.length_cons] at hi
        rw [show o + 8 * (i + 1) = o + 8 + 8 * i by omega, et i (by omega)]
        rfl
    · simp only [List.length_cons] at hx
      rw [Ot x (by omega), Ob x (by simp only [List.length]; omega), ka.2.1]

theorem ctx_congr {P : Par} {s t : State} (hc : Ctx P s) (hg : t.gpr = s.gpr) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Ctx P t := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := hc
  exact ⟨by rw [hg, hwr]; exact a, b, by rw [hg, hrd, hwr]; exact c, by rw [hg]; exact d,
    by rw [hg, hrd, hwr]; exact e, by rw [hg]; exact f, by rw [hg, hm]; exact g, h⟩

/-- The registers the loop starts with. -/
theorem vregs_ok (s : State) (n : Nat) :
    WP isa (.block (vregs n)) s fun t =>
      (t.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 KB ∧ t.gpr .r11 = 0 ∧
        t.gpr .rbx = (BitVec.ofNat 32 n).setWidth 64 ∧ t.gpr .rcx = s.gpr .rdi + BitVec.ofNat 64 KB ∧
        t.gpr .rdx = s.gpr .rdi + BitVec.ofNat 64 KB ∧ t.gpr .r9 = s.gpr .rdi + BitVec.ofNat 64 KB) ∧
      VG.Proof.X25519.X86_64.Keeps [.r10, .r11, .rbx, .rcx, .rdx, .r9] s t := by
  apply WP.of_runBlock
  simp only [vregs, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, Option.map_some, Option.bind_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have e : (BitVec.ofNat 32 KB).signExtend 64 = BitVec.ofNat 64 KB := by decide
  refine ⟨⟨?_, rfl, trivial, ?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [e]
  · rw [e]
  · rw [e]
  · rw [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem ofs_add (base : Addr) {d : Nat} (hd : d < 2 ^ 64) : ofs base (base + BitVec.ofNat 64 d) = d := by
  simp only [ofs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  omega

theorem unch_same {base : Addr} {W : List (Nat × Nat)} {m₁ m₂ m₃ : Mem} (h₁ : Unch base W m₁ m₂)
    (h₂ : Unch base W m₂ m₃) : Unch base W m₁ m₃ :=
  (h₁.trans h₂).mono fun _ hw => (List.mem_append.mp hw).elim id id

/-- What the vectors' code starts from: what it has of the joint multiplication, with the field elements
`E` in the slots it only reads, and the generator's table. -/
structure VBase (c : Joint.Cfg) (base T : Addr) (size u v : Nat) {G : Point Cv} (Q : Point Cv)
    (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) (E : Nat → Fe Cv) (s : State) : Prop where
  core : VCore c base T size u v Q row E s
  gtab : GTab base T size s

theorem VBase.unch {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s t : State} (hV : VLay c size)
    (h : VBase c base T size u v Q row E s) (hdi : t.gpr .rdi = s.gpr .rdi) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hs : t.syms = s.syms) (hu : Unch base vW s.mem t.mem) :
    VBase c base T size u v Q row E t :=
  ⟨h.core.unch hV hdi hrd hwr hu hs, ⟨by rw [hrd, hwr]; exact h.gtab.1, h.gtab.2⟩⟩

/-- What the vectors' code keeps: the registers but its own, and memory but the vectors' part of the
working space. -/
structure WKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .rbx] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Unch base vW s.mem t.mem

theorem WKeep.trans {base : Addr} {s t u : State} (h₁ : WKeep base s t) (h₂ : WKeep base t u) : WKeep base s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, unch_same h₁.mem h₂.mem⟩

theorem WKeep.of_vkeep {base : Addr} {s t : State} (hdi : s.gpr .rdi = base) (k : VKeep s t) : WKeep base s t :=
  ⟨fun r hr => k.gpr r fun h' => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
    rcases h' with h' | h' | h' | h' | h' | h' | h' | h' | h' <;> simp [h']), k.rd, k.wr,
    by have := k.mem; rw [hdi] at this; exact this.mono (by decide)⟩

/-- The constants written, the registers set and the accumulator's vectors zeroed. -/
theorem vinit_ok {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s : State} (hV : VLay c size)
    (h : VBase c base T size u v Q row E s) :
    WP isa (.block (fill kwords KB ++ (vregs (64 * c.K.M.n + 1) ++ zeroAcc))) s fun t =>
      (VBase c base T size u v Q row E t ∧ Ctx par t ∧ (∀ r, r < 20 → ∀ k, k < 4 → qv t (vreg r) k = 0) ∧
        t.gpr .r11 = 0 ∧ t.gpr .rbx = BitVec.ofNat 64 257 ∧ t.gpr .r10 = base + BitVec.ofNat 64 KB) ∧
      WKeep base s t ∧ t.gpr .r12 = s.gpr .r12 := by
  have hdi := h.core.field.scr.rdi
  have hbig := hV.big
  have hpool := hV.pool
  have hnw := h.core.field.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono_syms (fill_ok kwords h.core.field.scr (o := KB) (by rw [kwords_length]; simp only [KB]; omega))
    fun f ⟨fw, kf, Of⟩ sf => ?_
  rw [kwords_length] at fw Of
  have uf : Unch base [(6432, 1760)] s.mem f.mem := fun x hx => Of x (by
    have := hx (6432, 1760) (List.mem_singleton_self _)
    simp only [KB]; dsimp only at this; omega)
  have fdi : f.gpr .rdi = s.gpr .rdi := kf.gpr .rdi (by decide)
  have cf := h.core.unch hV fdi kf.rd kf.wr (uf.mono (by decide)) sf
  have hsf := cf.field.scr
  rw [WP.block_append_iff]
  refine WP.mono_syms (WP.skeep rfl (vregs_ok f _)) fun a ⟨⟨a10, a11, ab, acx, adx, a9⟩, ka⟩ sa => ?_
  rw [hsf.rdi] at a10 acx adx a9
  have va : VKeep f a := .of_skeep ka
  have hlim (b : Reg) : par.lim b ≤ 96 := by
    simp only [par]; split <;> (try split) <;> (try split) <;> omega
  have hreg (b : Reg) (d : Nat) (hd : d + 32 ≤ par.lim b) : a.gpr b = base + BitVec.ofNat 64 KB := by
    by_cases h1 : b = .rcx
    · subst h1; exact acx
    by_cases h2 : b = .rdx
    · subst h2; exact adx
    by_cases h3 : b = .r9
    · subst h3; exact a9
    rw [lim_other h1 h2 h3] at hd; omega
  have hrdK (d : Nat) (hd : d + 32 ≤ 1760) :
      InRegions (a.rd ++ a.wr) (base + BitVec.ofNat 64 KB + BitVec.ofNat 64 d) 32 := by
    rw [ka.rd, ka.wr, Offset.add_add]
    exact ⟨⟨base, size⟩, List.mem_append_right _ hsf.wr,
      Region.contains_off (Region.contains_self base size) (by simp only [KB]; omega)⟩
  have hca : Ctx par a := by
    refine ⟨fun d hd => ?_, by decide, fun b d _ _ hd => ?_, fun b d _ _ hd => ?_, fun d hd => ?_, fun d hd => ?_,
      fun i hi => ?_, by decide⟩
    · rw [ka.wr, ka.gpr .rdi (by decide), hsf.rdi]
      have hwin : par.win = 5920 := rfl
      exact ⟨⟨base, size⟩, hsf.wr, Region.contains_off (Region.contains_self base size) (by omega)⟩
    · rw [hreg b d hd]; exact hrdK d (by have := hlim b; omega)
    · rw [hreg b d hd, ka.gpr .rdi (by decide), hsf.rdi]
      exact sep_pool (by have := hlim b; omega)
    · rw [par_cst_length] at hd
      show InRegions _ (a.gpr .r10 + _) 32
      rw [a10]; exact hrdK d (by omega)
    · rw [par_cst_length] at hd
      show Mem.Sep (a.gpr .r10 + _) 32 _ _
      rw [a10, ka.gpr .rdi (by decide), hsf.rdi]
      exact sep_pool (by omega)
    · rw [par_cst_length] at hi
      show a.mem.readW (a.gpr .r10 + _) 64 = _
      have hw : f.mem.readW (base + BitVec.ofNat 64 (KB + 8 * i)) 64 = kwords.getD i 0 := fw i hi
      rw [a10, ka.mem, Offset.add_add, hw, kwords_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getD_eq_getElem?_getD]
      cases par.cst[i]? <;> rfl
  have ca := cf.vkeep hV va sa
  refine WP.mono_syms (zero_ok 20 a) fun t ⟨hz, hg, hm, hrd, hwr⟩ st => ?_
  have vt : VKeep a t := ⟨fun r _ => congrFun hg r, hrd, hwr, by rw [hm]; exact Unch.refl _ _ _⟩
  have ut : Unch base [(6432, 1760)] s.mem t.mem := by rw [hm, ka.mem]; exact uf
  refine ⟨⟨⟨ca.vkeep hV vt st,
    ⟨by rw [hrd, hwr, ka.rd, ka.wr, kf.rd, kf.wr]; exact h.gtab.1, h.gtab.2⟩⟩, ctx_congr hca hg hm hrd hwr,
    hz, by rw [hg]; exact a11, ?_, by rw [hg]; exact a10⟩, ⟨fun r hr => ?_,
    hrd.trans (ka.rd.trans kf.rd), hwr.trans (ka.wr.trans kf.wr), ut.mono (by decide)⟩,
    by rw [hg, ka.gpr .r12 (by decide), kf.gpr .r12 (by decide)]⟩
  · rw [hg, ab, hV.n]
    rfl
  · rw [hg, ka.gpr r (fun h' => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
      rcases h' with h' | h' | h' | h' | h' | h' <;> simp [h'])), kf.gpr r (fun h' => hr (by
      rw [List.mem_singleton] at h'; subst h'; decide))]

/-- `Q`'s multiples as limbs, and the accumulator's vectors zero again: the loop's invariant. -/
theorem vtabs_ok {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s : State} (hV : VLay c size)
    (h : VBase c base T size u v Q row E s) (hc : Ctx par s) (hz : ∀ r, r < 20 → ∀ k, k < 4 → qv s (vreg r) k = 0)
    (h11 : s.gpr .r11 = 0) (hb : s.gpr .rbx = BitVec.ofNat 64 257) (h10 : s.gpr .r10 = base + BitVec.ofNat 64 KB) :
    WP isa (.seq (vtab c) (.block zeroAcc)) s fun t =>
      VInv c base T (base + BitVec.ofNat 64 KB) size u v Q row E 257 none t ∧ WKeep base s t ∧
        t.gpr .r12 = s.gpr .r12 := by
  have hn := hV.n
  have tw (x : Nat) : toM pN (2 ^ 256) (wordsVal s.mem base x 4) = tmv Cv c.K.M.n base s x := by
    unfold tmv; rw [hn]; rfl
  apply WP.seq
  refine WP.mono_syms (vtab_ok h.core.field.scr hc (envOK_zero hz) h10 hV.pool hV.px hV.py
    ((tw _).trans (h.core.ro _ (by simp [winRo]))) ((tw _).trans (h.core.ro _ (by simp [winRo]))))
    fun a ⟨hca, ka, hqa⟩ sa => ?_
  have ua : Unch base vW s.mem a.mem := ka.mem.mono (by decide)
  have adi := ka.gpr .rdi (by decide)
  refine WP.mono_syms (zero_ok 20 a) fun t ⟨hzt, hg, hm, hrd, hwr⟩ st => ?_
  have ut : Unch base vW s.mem t.mem := by rw [hm]; exact ua
  have tdi : t.gpr .rdi = s.gpr .rdi := by rw [hg]; exact adi
  refine ⟨⟨h.core.unch hV tdi (hrd.trans ka.rd) (hwr.trans ka.wr) ut (st.trans sa),
      ⟨by rw [hrd, hwr, ka.rd, ka.wr]; exact h.gtab.1, h.gtab.2⟩, ctx_congr hca hg hm hrd hwr, envOK_zero hzt,
      by rw [hm]; exact hqa, ?_, by rw [hg]; exact (ka.gpr .rbx (by decide)).trans hb,
      by rw [hg]; exact (ka.gpr .r10 (by decide)).trans h10⟩,
    ⟨fun r hr => ?_, hrd.trans ka.rd, hwr.trans ka.wr, ut⟩, by rw [hg]; exact ka.gpr .r12 (by decide)⟩
  · show t.gpr .r11 = 0
    rw [hg]; exact (ka.gpr .r11 (by decide)).trans h11
  · rw [hg]
    exact ka.gpr r (fun h' => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
      rcases h' with h' | h' | h' | h' <;> simp [h']))

/-! ### The loop -/

theorem vdigits_ok {c : Joint.Cfg} {base T K : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s : State} (hV : VLay c size)
    (h9 : c.gw = 9) (h : VInv c base T K size u v Q row E 257 none s) :
    WP isa (.loop (vstep c) .ne) s fun t =>
      VInv c base T K size u v Q row E 0 (accN c row (tqE c E) u v 257) t ∧ VKeep s t := by
  apply countLoop_ok (Inv := fun j t =>
    VInv c base T K size u v Q row E j (accN c row (tqE c E) u v (257 - j)) t ∧ VKeep s t) (n := 257)
  · intro j a hj1 hj ⟨hi, hk⟩
    have he : j - 1 + 1 = j := by omega
    have hi' : VInv c base T K size u v Q row E (j - 1 + 1) (accN c row (tqE c E) u v (257 - j)) a := by
      rw [he]; exact hi
    refine WP.mono (vstep_ok hV h9 (j := j - 1) (by omega) hi')
      fun t ⟨⟨it, tz⟩, kt⟩ => ⟨⟨?_, hk.trans kt⟩, tz⟩
    have e : 257 - (j - 1) = (257 - j) + 1 := by omega
    rw [e, accN, show 256 - (257 - j) = j - 1 by omega]
    exact it
  · intro t ht; exact ht
  · decide
  · exact ⟨h, VKeep.refl s⟩

/-! ### Out of the vectors -/

def stSeg : Seg Id T := fun ins => pure ins

def slots5 : List Loc := (List.range 5).map .slot

/-- The first five slots, as the rows of a vector of five limbs. -/
abbrev sl5 : F5 T := (leaves slots5).getD 0 zero5

theorem st_chk : chkSeg storeOut [t5 0] stSeg slots5 = true := by decide +kernel

theorem st_iv : ivWithin (bndsOf regs5 outBT2) (segT stSeg [t5 0]) outBT2 = true := by decide +kernel

theorem st_ov : ovOk outBT2 outBT2 [] = true := by decide +kernel

theorem storeOut_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf regs5 outBT2)) {a b c : Fin pN}
    (h : Car3 (envOf s₀) (t5 0) a b c) :
    WP isa (.block storeOut) s₀ fun s => Kept s₀ s ∧ Car3 (envOf s) sl5 a b c := by
  refine WP.mono (cut_step' st_chk hc hB st_iv st_ov (rs := [t5 0]) rfl rfl (Nat.le_of_eq rfl)
    (fun _ _ hm => nomatch hm)) fun s ⟨_, hk, _, hS⟩ => ⟨hk, ?_⟩
  exact ⟨hS.car 0 0 (by decide) rfl rfl h.y, hS.car 0 1 (by decide) rfl rfl h.z, hS.car 0 3 (by decide) rfl rfl h.x⟩

/-- What the loop leaves: nothing if no digit was set; else the rows of the accumulator's triple, times
`4 · 2²⁵⁶`, `4 · 2²⁵⁶` and `2 · 2²⁵⁶`, in the slots. -/
def OutSt (t : State) : Option (Fin pN × Fin pN × Fin pN) → Prop
  | none => t.gpr .r11 = 0
  | some a => t.gpr .r11 = 1 ∧
      Car3 (envOf t) sl5 (a.2.1 * D (c4R : Nat)) (a.2.2 * D (c2R : Nat)) (a.1 * D (c4R : Nat))

/-- What the loop leaves. -/
structure VOut (c : Joint.Cfg) (base T : Addr) (size u v : Nat) {G : Point Cv} (Q : Point Cv)
    (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) (E : Nat → Fe Cv)
    (acc : Option (Fin pN × Fin pN × Fin pN)) (t : State) : Prop where
  core : VCore c base T size u v Q row E t
  out : OutSt t acc

/-- Out of the vectors, if the accumulator is set. -/
theorem vout_ok {c : Joint.Cfg} {base T K : Addr} {size u v j : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {b : State} (hV : VLay c size)
    (ib : VInv c base T K size u v Q row E j acc b) :
    WP isa (.seq (.block [.alu .test .r11 (.reg .r11)])
      (.ite .e (.block []) (.block (outPieces.flatten ++ storeOut)))) b fun t =>
      VOut c base T size u v Q row E acc t ∧ VKeep b t := by
  apply WP.seq
  refine WP.mono_syms (WP.skeep rfl (test_ok b .r11)) fun d ⟨dz, kd⟩ sd => ?_
  have vd : VKeep b d := .of_skeep kd
  have id := ib.skeep hV kd sd
  cases acc with
  | none =>
    have h0 : b.gpr .r11 = 0 := ib.acc
    exact WP.ite true (by show d.zf = _; rw [dz, h0]; rfl)
      (fun _ => WP.block_nil ⟨⟨id.core, id.acc⟩, vd⟩) (fun h => nomatch h)
  | some x =>
    refine WP.ite false (by show d.zf = _; rw [dz, ib.acc.1]; rfl) (fun h => nomatch h) (fun _ => ?_)
    rw [WP.block_append_iff]
    refine WP.mono_syms (out_ok id.ctx id.env id.acc.2) fun e ⟨hce, ke, hBe, he⟩ se => ?_
    refine WP.mono_syms (storeOut_ok hce hBe he) fun t ⟨kt, ht⟩ st => ?_
    have ve : VKeep d e := .of_lkeep (.of_kept ke)
    have vt : VKeep e t := .of_lkeep (.of_kept kt)
    have ce := id.core.vkeep hV ve se
    exact ⟨⟨ce.vkeep hV vt st, by rw [kt.gpr, ke.gpr]; exact id.acc.1, ht⟩, (vd.trans ve).trans vt⟩

/-- The loop over the digits. -/
theorem vloop_ok {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s : State} (hV : VLay c size)
    (h9 : c.gw = 9) (h : VBase c base T size u v Q row E s) :
    WP isa (vloop c) s fun t => VOut c base T size u v Q row E (accN c row (tqE c E) u v 257) t ∧
      WKeep base s t ∧ t.gpr .r12 = s.gpr .r12 := by
  rw [vloop]
  apply WP.seq
  refine WP.mono (vinit_ok hV h) fun a₀ ⟨⟨b₀, c₀, z₀, h11, hb, h10⟩, k₀, r₀⟩ => ?_
  apply WP.seq
  refine WP.mono (vtabs_ok hV b₀ c₀ z₀ h11 hb h10) fun a ⟨ia, ka', ra'⟩ => ?_
  have ka := k₀.trans ka'
  have ra := ra'.trans r₀
  have adi := ia.core.field.scr.rdi
  apply WP.seq
  refine WP.mono (vdigits_ok hV h9 ia) fun b ⟨ib, kb⟩ => ?_
  have bdi := ib.core.field.scr.rdi
  exact WP.mono (vout_ok hV ib) fun t ⟨ot, kt⟩ => ⟨ot, (ka.trans (.of_vkeep adi kb)).trans (.of_vkeep bdi kt),
    by rw [kt.gpr .r12 (by decide), kb.gpr .r12 (by decide), ra]⟩

/-! ### MXCSR -/

theorem ea_sc' (t : State) (d : Nat) : t.ea (sc d) = t.gpr .rdi + BitVec.ofNat 64 d := ea_sc t d

theorem scr_in {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat} (hd : d + n ≤ size) :
    InRegions s.wr (base + BitVec.ofNat 64 d) n :=
  ⟨_, hs.wr, Region.contains_off (Region.contains_self base size) hd⟩

theorem scr_in' {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat} (hd : d + n ≤ size) :
    InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 d) n :=
  let ⟨r, h, c⟩ := scr_in hs hd; ⟨r, List.mem_append_right _ h, c⟩

section
open VG.Proof.MlKem.X86_64

/-- The prologue's first half: the caller's MXCSR, bits 31:16 cleared, in `r12`. -/
theorem mxSave_ok {s : State} {base : Addr} {size mx : Nat} (hs : Scr s base size) (hsz : mx + 8 ≤ size) :
    WP isa (.block [.stmxcsr (sc mx), .mov32 .r12 (.mem (sc mx)), .alu32 .and .r12 (.imm 0xFFFF)]) s fun s' =>
      (s'.mem = s.mem.writeW (base + BitVec.ofNat 64 mx) s.mxcsr ∧
        s'.gpr .r12 = (s.mxcsr &&& 0xFFFF).setWidth 64) ∧ Keep [.r12] s s' := by
  have hst : InRegions s.wr (base + BitVec.ofNat 64 mx) 4 := scr_in hs (by omega)
  have hld : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 mx) 4 := scr_in' hs (by omega)
  have hdi := hs.rdi
  refine WP.keep [.r12] (Q := fun s' => s'.mem = s.mem.writeW (base + BitVec.ofNat 64 mx) s.mxcsr ∧
    s'.gpr .r12 = (s.mxcsr &&& 0xFFFF).setWidth 64) (by
    xrun [ea_sc', hdi, hst, hld, Mem.readW_writeW_self32]) rfl

/-- The prologue's second half: `MXCSR := 0x1FBF`. -/
theorem mxSet_ok {s : State} {base : Addr} {size mx : Nat} (hs : Scr s base size) (hsz : mx + 8 ≤ size) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (sc (mx + 4)) .rax, .ldmxcsr (sc (mx + 4)), .lfence]) s
      fun s' => s'.mem = s.mem.writeW (base + BitVec.ofNat 64 (mx + 4)) (0x1FBF : BitVec 32) ∧ Keep [.rax] s s' := by
  have hst : InRegions s.wr (base + BitVec.ofNat 64 (mx + 4)) 4 := scr_in hs (by omega)
  have hld : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (mx + 4)) 4 := scr_in' hs (by omega)
  have hdi := hs.rdi
  refine WP.keep [.rax] (Q := fun s' => s'.mem = s.mem.writeW (base + BitVec.ofNat 64 (mx + 4)) (0x1FBF : BitVec 32))
    (by xrun [ea_sc', hdi, hst, hld, Mem.readW_writeW_self32]) rfl

theorem and_ffff_hi (x : BitVec 32) : (x &&& 0xFFFF).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  rw [show (0xFFFF : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat]
  simp only [Nat.testBit_two_pow_sub_one]
  simp

/-- `vzeroupper` keeps the registers and memory. -/
theorem vzu_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun t => t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [WP.block_cons_iff]
  exact ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The epilogue: MXCSR from `r12`. -/
theorem mxRestore_ok {s : State} {base : Addr} {size mx : Nat} {v : BitVec 32} (hs : Scr s base size)
    (hsz : mx + 8 ≤ size) (hv : s.gpr .r12 = (v &&& 0xFFFF).setWidth 64) :
    WP isa (.block [.store32 (sc mx) .r12, .ldmxcsr (sc mx)]) s fun s' =>
      s'.mem = s.mem.writeW (base + BitVec.ofNat 64 mx) ((s.gpr .r12).setWidth 32) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hst : InRegions s.wr (base + BitVec.ofNat 64 mx) 4 := scr_in hs (by omega)
  have hld : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 mx) 4 := scr_in' hs (by omega)
  have hdi := hs.rdi
  xrun [ea_sc', hdi, hv, hst, hld, Mem.readW_writeW_self32, and_ffff_hi]

end

theorem unch_write32 (m : Mem) (base : Addr) {d lo n : Nat} (v : BitVec 32) (h1 : lo ≤ d) (h2 : d + 4 ≤ lo + n)
    (h3 : d + 4 ≤ 2 ^ 64) : Unch base [(lo, n)] m (m.writeW (base + BitVec.ofNat 64 d) v) := by
  intro x hx
  have hx' := hx (lo, n) (List.mem_singleton_self _)
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx'
  omega

/-- MXCSR saved in `r12`, with its bits from 16 up clear. -/
def MxOk (t : State) : Prop := ∃ v : BitVec 32, t.gpr .r12 = (v &&& 0xFFFF).setWidth 64

/-- The prologue's first half, from the vectors' start. -/
theorem mxSave_vs {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s : State} (hV : VLay c size)
    (h : VBase c base T size u v Q row E s) :
    WP isa (.block [.stmxcsr (sc MXV), .mov32 .r12 (.mem (sc MXV)), .alu32 .and .r12 (.imm 0xFFFF)]) s fun t =>
      (VBase c base T size u v Q row E t ∧ MxOk t) ∧ WKeep base s t := by
  refine WP.mono_syms (mxSave_ok h.core.field.scr hV.mx) fun t ⟨⟨hm, h12⟩, kt⟩ st => ?_
  have ut : Unch base vW s.mem t.mem := by
    rw [hm]
    exact (unch_write32 (d := MXV) (lo := 5864) (n := 8) _ base _ (by decide) (by decide) (by decide)).mono (by decide)
  exact ⟨⟨h.unch hV (kt.1 .rdi (by decide)) kt.2.1 kt.2.2 st ut, s.mxcsr, h12⟩,
    fun r hr => kt.1 r (fun h' => hr (by rw [List.mem_singleton] at h'; subst h'; decide)), kt.2.1, kt.2.2, ut⟩

/-- The prologue's second half. -/
theorem mxSet_vs {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s : State} (hV : VLay c size)
    (h : VBase c base T size u v Q row E s) (hx : MxOk s) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (sc (MXV + 4)) .rax, .ldmxcsr (sc (MXV + 4)), .lfence]) s
      fun t => (VBase c base T size u v Q row E t ∧ MxOk t) ∧ WKeep base s t := by
  refine WP.mono_syms (mxSet_ok h.core.field.scr hV.mx) fun t ⟨hm, kt⟩ st => ?_
  have u1 : Unch base [(5868, 4)] s.mem t.mem := by
    rw [hm]; exact unch_write32 (d := MXV + 4) _ base _ (by decide) (by decide) (by decide)
  have ut : Unch base vW s.mem t.mem := u1.cover (by decide)
  obtain ⟨w, hw⟩ := hx
  exact ⟨⟨h.unch hV (kt.1 .rdi (by decide)) kt.2.1 kt.2.2 st ut, w, (kt.1 .r12 (by decide)).trans hw⟩,
    fun r hr => kt.1 r (fun h' => hr (by rw [List.mem_singleton] at h'; subst h'; decide)), kt.2.1, kt.2.2, ut⟩

/-! ### Out of the slots -/

/-- Five limbs at `d0`, …, `d4` of the working space into four words and what is above them. -/
def packCode (d0 d1 d2 d3 d4 : Nat) : List Instr :=
  [.mov .r8 (.mem (sc d0)), .mov .rax (.mem (sc d1)), .mov .r9 (.reg .rax), .shift .shl .rax 52,
    .alu .or .r8 (.reg .rax), .shift .shr .r9 12, .mov .rax (.mem (sc d2)), .mov .r10 (.reg .rax),
    .shift .shl .rax 40, .alu .or .r9 (.reg .rax), .shift .shr .r10 24, .mov .rax (.mem (sc d3)),
    .mov .r11 (.reg .rax), .shift .shl .rax 28, .alu .or .r10 (.reg .rax), .shift .shr .r11 36,
    .mov .rax (.mem (sc d4)), .mov .r12 (.reg .rax), .shift .shl .rax 16, .alu .or .r11 (.reg .rax),
    .shift .shr .r12 48]

theorem or_shl {a : Nat} (b : Nat) {k : Nat} (hk : k ≤ 64) (ha : a < 2 ^ k) :
    a ||| (b * 2 ^ k % 2 ^ 64) = a + b % 2 ^ (64 - k) * 2 ^ k := by
  have e : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_mod_mul_right, Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq,
    Nat.add_comm]

/-- Five limbs below `2⁵²` as four words and what is above them. -/
theorem pack_val (w0 w1 w2 w3 w4 : BitVec 64) (h0 : w0.toNat < 2 ^ 52) (h1 : w1.toNat < 2 ^ 52)
    (h2 : w2.toNat < 2 ^ 52) (h3 : w3.toNat < 2 ^ 52) :
    (w0 ||| w1 <<< 52).toNat + 2 ^ 64 * ((w1 >>> 12 ||| w2 <<< 40).toNat + 2 ^ 64 * ((w2 >>> 24 ||| w3 <<< 28).toNat +
      2 ^ 64 * ((w3 >>> 36 ||| w4 <<< 16).toNat + 2 ^ 64 * 0))) + 2 ^ 256 * (w4 >>> 48).toNat =
    w0.toNat + 2 ^ 52 * w1.toNat + 2 ^ 104 * w2.toNat + 2 ^ 156 * w3.toNat + 2 ^ 208 * w4.toNat := by
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [or_shl _ (by decide) h0, or_shl (k := 40) _ (by decide) (by omega), or_shl (k := 28) _ (by decide) (by omega),
    or_shl (k := 16) _ (by decide) (by omega)]
  omega

section
open VG.Proof.MlKem.X86_64

theorem packCode_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d0 d1 d2 d3 d4 : Nat}
    (h0 : d0 + 8 ≤ size) (h1 : d1 + 8 ≤ size) (h2 : d2 + 8 ≤ size) (h3 : d3 + 8 ≤ size) (h4 : d4 + 8 ≤ size)
    (b0 : (s.mem.readW (base + BitVec.ofNat 64 d0) 64).toNat < 2 ^ 52)
    (b1 : (s.mem.readW (base + BitVec.ofNat 64 d1) 64).toNat < 2 ^ 52)
    (b2 : (s.mem.readW (base + BitVec.ofNat 64 d2) 64).toNat < 2 ^ 52)
    (b3 : (s.mem.readW (base + BitVec.ofNat 64 d3) 64).toNat < 2 ^ 52) :
    WP isa (.block (packCode d0 d1 d2 d3 d4)) s fun t =>
      (regsVal t [.r8, .r9, .r10, .r11] + 2 ^ 256 * (t.gpr .r12).toNat =
        (s.mem.readW (base + BitVec.ofNat 64 d0) 64).toNat + 2 ^ 52 * (s.mem.readW (base + BitVec.ofNat 64 d1) 64).toNat +
        2 ^ 104 * (s.mem.readW (base + BitVec.ofNat 64 d2) 64).toNat +
        2 ^ 156 * (s.mem.readW (base + BitVec.ofNat 64 d3) 64).toNat +
        2 ^ 208 * (s.mem.readW (base + BitVec.ofNat 64 d4) 64).toNat ∧ t.mem = s.mem) ∧
      Keep [.rax, .r8, .r9, .r10, .r11, .r12] s t := by
  have hdi := hs.rdi
  have r0 := scr_in' hs h0; have r1 := scr_in' hs h1; have r2 := scr_in' hs h2
  have r3 := scr_in' hs h3; have r4 := scr_in' hs h4
  refine WP.keep _ ?_ rfl
  rw [packCode]
  xrun [ea_sc', hdi, r0, r1, r2, r3, r4]
  simp only [regsVal, setReg_gpr, setFlags_gpr, reduceCtorEq, ↓reduceIte]
  exact pack_val _ _ _ _ _ b0 b1 b2 b3

end


theorem sl5_limb (s : State) (l : Nat) : ∀ i, i < 5 → (sl5.get i).int (envOf s) l =
    (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (SL + 32 * i + 8 * l)) 64).toInt := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem toNat_of_toInt (x : BitVec 64) (h0 : 0 ≤ x.toInt) (h1 : x.toInt < 2 ^ 52) :
    (x.toNat : Int) = x.toInt ∧ x.toNat < 2 ^ 52 := by
  have := x.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h0 h1 ⊢
  split at h0 <;> omega

theorem val5_nat (w0 w1 w2 w3 w4 : Nat) : val5 w0 w1 w2 w3 w4 =
    ((w0 + 2 ^ 52 * w1 + 2 ^ 104 * w2 + 2 ^ 156 * w3 + 2 ^ 208 * w4 : Nat) : Int) := by
  simp only [val5]
  omega

theorem packLaneAt_eq (sl : Nat) (M : Mod) (l dst : Nat) : packLaneAt sl M l dst =
    packCode (sl + 32 * 0 + 8 * l) (sl + 32 * 1 + 8 * l) (sl + 32 * 2 + 8 * l) (sl + 32 * 3 + 8 * l)
      (sl + 32 * 4 + 8 * l) ++ (csubC M [.r8, .r9, .r10, .r11] .r12 ++
        VG.Impl.Mont.X86_64.stores [.r8, .r9, .r10, .r11] dst) := by
  unfold packLaneAt
  rw [List.append_assoc]
  rfl

/-- Five words at `sl`, `32` bytes apart, as limbs below `2⁵²` of a number below `2 p`, reduced into the
words at `dst`. -/
theorem packLaneAt_ok {M : Mod} {s : State} {base : Addr} {size m sl : Nat} (hs : Scr s base size)
    (hbig : sl + 160 ≤ size) (hn : M.n = 4) (hmo : M.mo + 8 * M.n ≤ size) (hm : wordsVal s.mem base M.mo M.n = m)
    (hm2 : Nb ≤ 2 * (m : Int)) {l dst : Nat} (hl : l < 4) (hdst : dst + 32 ≤ size)
    (hw : ∀ i, i < 5 → 0 ≤ (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * i + 8 * l)) 64).toInt ∧
      (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * i + 8 * l)) 64).toInt < 2 ^ 52)
    (hlt : val5 (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 0 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 1 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 2 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 3 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 4 + 8 * l)) 64).toInt < Nb) :
    WP isa (.block (packLaneAt sl M l dst)) s fun t =>
      wordsVal t.mem base dst 4 = (val5 (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 0 + 8 * l)) 64).toInt
        (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 1 + 8 * l)) 64).toInt
        (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 2 + 8 * l)) 64).toInt
        (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 3 + 8 * l)) 64).toInt
        (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 4 + 8 * l)) 64).toInt).toNat % m ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12] s t ∧ Outside base dst 32 s.mem t.mem := by
  have hdi := hs.rdi
  obtain ⟨c0, b0⟩ := toNat_of_toInt _ (hw 0 (by decide)).1 (hw 0 (by decide)).2
  obtain ⟨c1, b1⟩ := toNat_of_toInt _ (hw 1 (by decide)).1 (hw 1 (by decide)).2
  obtain ⟨c2, b2⟩ := toNat_of_toInt _ (hw 2 (by decide)).1 (hw 2 (by decide)).2
  obtain ⟨c3, b3⟩ := toNat_of_toInt _ (hw 3 (by decide)).1 (hw 3 (by decide)).2
  obtain ⟨c4, -⟩ := toNat_of_toInt _ (hw 4 (by decide)).1 (hw 4 (by decide)).2
  obtain ⟨N, hN, hv'⟩ : ∃ N : Nat, N =
      (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 0 + 8 * l)) 64).toNat +
      2 ^ 52 * (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 1 + 8 * l)) 64).toNat +
      2 ^ 104 * (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 2 + 8 * l)) 64).toNat +
      2 ^ 156 * (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 3 + 8 * l)) 64).toNat +
      2 ^ 208 * (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 4 + 8 * l)) 64).toNat ∧
      val5 (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 0 + 8 * l)) 64).toInt
        (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 1 + 8 * l)) 64).toInt
        (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 2 + 8 * l)) 64).toInt
        (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 3 + 8 * l)) 64).toInt
        (s.mem.readW (base + BitVec.ofNat 64 (sl + 32 * 4 + 8 * l)) 64).toInt = (N : Int) := by
    refine ⟨_, rfl, ?_⟩
    rw [← c0, ← c1, ← c2, ← c3, ← c4, val5_nat]
  rw [hv'] at hlt ⊢
  rw [Int.toNat_natCast]
  have hN2 : N < 2 * m := by omega
  rw [packLaneAt_eq, WP.block_append_iff]
  refine WP.mono (packCode_ok hs (by omega) (by omega) (by omega) (by omega) (by omega) b0 b1 b2 b3)
    fun a ⟨⟨hv, hmem⟩, ka⟩ => ?_
  rw [← hN] at hv
  have hsa : Scr a base size := ⟨(ka.1 .rdi (by decide)).trans hdi, ka.2.2 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  have e64 : 2 ^ (64 * M.n) = 2 ^ 256 := by rw [hn]
  refine WP.mono (csubC_ok hsa (ts := [.r8, .r9, .r10, .r11]) (top := .r12) (by rw [hn]; rfl) (by omega) (by omega)
    ⟨by decide, by decide⟩ hmo (m := m) (by rw [hmem]; exact hm) (by rw [e64, hv]; exact hN2))
    fun b ⟨hb, kb⟩ => ?_
  rw [e64, hv] at hb
  have hsb : Scr b base size := ⟨(kb.1 .rdi (by decide)).trans hsa.rdi, kb.2.2.2 ▸ hsa.wr, hs.nowrap⟩
  refine WP.mono (stores_ok [.r8, .r9, .r10, .r11] hsb (o := dst) (by simp only [List.length]; omega) (by decide))
    fun t ⟨ht, kt, ot⟩ => ?_
  refine ⟨?_, ⟨fun r hr => ?_, kt.rd.trans (kb.2.2.1.trans ka.2.1), kt.wr.trans (kb.2.2.2.trans ka.2.2)⟩, ?_⟩
  · have e : [Reg.r8, Reg.r9, Reg.r10, Reg.r11].length = 4 := rfl
    rw [e] at ht
    rw [ht, hb]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.gpr r List.not_mem_nil, kb.1 r (by simp [hr]), ka.1 r (by simp [hr])]
  · intro z hz
    rw [ot z hz, kb.2.1, hmem]

/-- A lane of the slots, carried and below `2 p`, reduced into the words at `dst`. -/
theorem packLane_ok {M : Mod} {s : State} {base : Addr} {size m : Nat} (hs : Scr s base size) (hbig : 5920 ≤ size)
    (hn : M.n = 4) (hmo : M.mo + 8 * M.n ≤ size) (hm : wordsVal s.mem base M.mo M.n = m) (hm2 : Nb ≤ 2 * (m : Int))
    {l dst : Nat} (hl : l < 4) (hdst : dst + 32 ≤ size) {x : Fin pN} (hc : Car (envOf s) l sl5 x) :
    WP isa (.block (packLane M l dst)) s fun t =>
      wordsVal t.mem base dst 4 = (vI (envOf s) l sl5).toNat % m ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12] s t ∧ Outside base dst 32 s.mem t.mem := by
  have hdi := hs.rdi
  have key (i : Nat) (hi : i < 5) :
      (0 ≤ (s.mem.readW (base + BitVec.ofNat 64 (SL + 32 * i + 8 * l)) 64).toInt ∧
        (s.mem.readW (base + BitVec.ofNat 64 (SL + 32 * i + 8 * l)) 64).toInt < 2 ^ 52) ∧
      (sl5.get i).int (envOf s) l = (s.mem.readW (base + BitVec.ofNat 64 (SL + 32 * i + 8 * l)) 64).toInt := by
    have e := sl5_limb s l i hi
    have b := hc.c.get hi
    rw [hdi] at e
    rw [e] at b
    exact ⟨b, e⟩
  have ev : vI (envOf s) l sl5 = val5 (s.mem.readW (base + BitVec.ofNat 64 (SL + 32 * 0 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (SL + 32 * 1 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (SL + 32 * 2 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (SL + 32 * 3 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (SL + 32 * 4 + 8 * l)) 64).toInt := by
    rw [vI_get, (key 0 (by decide)).2, (key 1 (by decide)).2, (key 2 (by decide)).2, (key 3 (by decide)).2,
      (key 4 (by decide)).2]
  rw [ev]
  exact packLaneAt_ok hs (by simp only [SL]; omega) hn hmo hm hm2 hl hdst (fun i hi => (key i hi).1)
    (by rw [← ev]; exact hc.hi)


/-- A lane of the slots depends only on the slots' words. -/
theorem lim_sl5_congr {E E' : Env} {k : Nat}
    (h : ∀ i, i < 5 → E'.m .rdi (slotOff i) k = E.m .rdi (slotOff i) k) {bd : Int} {x : Fin pN}
    (hc : Lim bd E k sl5 x) : Lim bd E' k sl5 x := by
  have e0 : sl5.l0.int E' k = sl5.l0.int E k := h 0 (by decide)
  have e1 : sl5.l1.int E' k = sl5.l1.int E k := h 1 (by decide)
  have e2 : sl5.l2.int E' k = sl5.l2.int E k := h 2 (by decide)
  have e3 : sl5.l3.int E' k = sl5.l3.int E k := h 3 (by decide)
  have e4 : sl5.l4.int E' k = sl5.l4.int E k := h 4 (by decide)
  have ev : vI E' k sl5 = vI E k sl5 := by simp only [vI, e0, e1, e2, e3, e4]
  refine ⟨?_, by rw [ev]; exact hc.hi, by rw [ev]; exact hc.d⟩
  have := hc.c
  unfold Carried at this ⊢
  rw [e0, e1, e2, e3, e4]
  exact this

/-- The words of a carried lane that stands for `c · 2²⁵⁶ x`, reduced, are `c x` as a multiple of `2²⁵⁶`. -/
theorem toM_car {E : Env} {k : Nat} {v : F5 T} {x : Fin pN} (cc : Nat)
    (hc : Car E k v (x * D ((cc * 2 ^ 256 % pN : Nat) : Int))) :
    toM pN (2 ^ 256) ((vI E k v).toNat % pN) = Fin.ofNat pN cc * x := by
  have h0 := hc.lo
  have e := out_mont cc hc.d
  have e' : ofI pN (vI E k v) = Fin.ofNat pN (vI E k v).toNat :=
    calc ofI pN (vI E k v) = ofI pN (((vI E k v).toNat : Nat) : Int) := by rw [Int.toNat_of_nonneg h0]
      _ = _ := ofI_natCast _
  have hu := mul_rinv (unitMod_pow_two (m := pN) (by decide) 256)
  unfold toM
  rw [ofNat_mod, ← e', e]
  grind

theorem pk_regs {n : Nat} (hn : n = 4) :
    ∀ r ∈ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12], r ∈ clob n := by
  subst hn; decide

theorem jointWork_R (c : Joint.Cfg) : ∀ x ∈ jacCoords c.K.R, x ∈ jointWork c := by
  intro w hw
  simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [jointWork, winOther, List.mem_append, List.mem_cons]
  rcases hw with rfl | rfl | rfl <;> simp

/-- The loop's input and the fields it only reads are kept by code that writes only the joint
multiplication's working slots. -/
theorem jwi_work {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {s t : State} (hL : JointLayout c size)
    (hs : Scr s base size) (htmp : c.K.M.tmp + 8 * c.K.M.n ≤ size)
    (hw : JointWindowInput c Cv base T size u v Q row s) (kw : ProgKeep c.K.M base (jointWork c) s t)
    (hy : t.syms = s.syms) :
    JointWindowInput c Cv base T size u v Q row t ∧
      ∀ x ∈ winRo c.K, tmv Cv c.K.M.n base t x = tmv Cv c.K.M.n base s x := by
  have hnw := hs.nowrap
  have hro (x : Nat) (hx : x ∈ winRo c.K) : tmv Cv c.K.M.n base t x = tmv Cv c.K.M.n base s x := by
    have hr : (x, 8 * c.K.M.n) ∈ jointStableRanges c :=
      List.mem_append_left _ (List.mem_map.mpr ⟨x, List.mem_append_left _ (List.mem_append_left _ hx), rfl⟩)
    unfold tmv
    rw [kw.unch.wordsVal (hL.stableSep _ hr) (by have := hL.stableBounds _ hr; dsimp only at this; omega)]
  have hbits (d l : Nat) (ho : (d, l) ∈ jointStableRanges c) (j : Nat) (hj : j < l) :
      t.mem (off base (d + j)) = s.mem (off base (d + j)) := by
    apply kw.unch.byte
    · intro w hw'
      have := hL.stableSep _ ho w hw'
      dsimp only at this ⊢; omega
    · have := hL.stableBounds _ ho; dsimp only at this; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, JointGenerator.workKeep hL htmp s t kw hy hw.external⟩, hro⟩
  · rw [hro _ (by simp [winRo]), hro _ (by simp [winRo]), hro _ (by simp [winRo])]
    exact hw.point
  · rw [hro _ (by simp [winRo])]
    exact hw.affine
  · rw [hro _ (by simp [winRo])]
    exact hw.zero
  · intro j hj
    rw [hbits c.K.bits _ (by simp [jointStableRanges]) j hj]
    exact hw.peer j hj
  · intro j hj
    rw [hbits c.gBits _ (by simp [jointStableRanges]) j hj]
    exact hw.generator j hj

/-- A lane of the slots into a coordinate of `R`. -/
theorem lane_ok {c : Joint.Cfg} {base : Addr} {size : Nat} {E : Nat → Fe Cv} {s : State} (hV : VLay c size)
    (hL : Lay c.K.M size (· ∈ nafSlots c.K))
    (hi : Inv c.K.M base size Cv.p (· ∈ nafSlots c.K) (winRo c.K ++ jacCoords c.K.R) E s) {l dst : Nat}
    (hl : l < 4) (hd : dst ∈ jacCoords c.K.R) {x : Fin pN} (cc : Nat)
    (hc : Car (envOf s) l sl5 (x * D ((cc * 2 ^ 256 % pN : Nat) : Int))) :
    WP isa (.block (packLane c.K.M l dst)) s fun t =>
      ProgKeep c.K.M base [dst] s t ∧
      Inv c.K.M base size Cv.p (· ∈ nafSlots c.K) (winRo c.K ++ jacCoords c.K.R)
        (fun y => toM Cv.p (2 ^ (64 * c.K.M.n)) (wordsVal t.mem base y c.K.M.n)) t ∧
      toM Cv.p (2 ^ (64 * c.K.M.n)) (wordsVal t.mem base dst c.K.M.n) = Fin.ofNat pN cc * x ∧
      ∀ i, i < 5 → ∀ k, k < 4 → (envOf t).m .rdi (slotOff i) k = (envOf s).m .rdi (slotOff i) k := by
  have hn := hV.n
  have hs := hi.scr
  have hnw := hs.nowrap
  have hbig := hV.big
  have hSl : dst ∈ nafSlots c.K := hi.sl dst (List.mem_append_right _ hd)
  have hle := hL.le dst hSl
  have hliv := hV.live dst (List.mem_append_right _ hd) (5056, 288) (by simp [vW])
  rw [hn] at hle hliv
  dsimp only at hliv
  refine WP.mono (packLane_ok hs hV.big hn hi.mod.mo hi.mod.val (by decide +kernel) hl hle hc)
    fun t ⟨hv, kt, ot⟩ => ?_
  have kp : ProgKeep c.K.M base [dst] s t := ⟨fun r hr => kt.gpr r (fun h' => hr (pk_regs hn r h')), kt.rd, kt.wr,
    fun z hz _ => ot z (by have := hz dst (List.mem_singleton_self _); rw [hn] at this; omega)⟩
  have hlt : ∀ y ∈ [dst], wordsVal t.mem base y c.K.M.n < Cv.p := by
    intro y hy
    rw [List.mem_singleton] at hy; subst hy
    rw [hn, hv]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))
  have it := (Inv.of_progKeep hL hi kp (fun y hy => by rw [List.mem_singleton] at hy; subst hy; exact hSl)
    hlt).sub (fun y hy => List.mem_append_right _ hy)
  refine ⟨kp, it, ?_, fun i hi' k hk => ?_⟩
  · rw [hn, hv]
    exact toM_car cc hc
  · show (t.mem.readW (t.gpr .rdi + _) 64).toInt = (s.mem.readW (s.gpr .rdi + _) 64).toInt
    rw [kt.gpr .rdi (by decide), hs.rdi]
    congr 1
    apply Mem.readW_congr
    intro j hj
    have hsb : cfg.sbase = 5056 := rfl
    rw [Offset.add_add]
    exact ot _ (by rw [ofs_add base (by simp only [slotOff, hsb]; omega)]; simp only [slotOff, hsb]; omega)


/-- What the loop left, with its flag in `rbx`. -/
def PackSt (t : State) : Option (Fin pN × Fin pN × Fin pN) → Prop
  | none => t.gpr .rbx = 0
  | some a => t.gpr .rbx = 1 ∧
      Car3 (envOf t) sl5 (a.2.1 * D (c4R : Nat)) (a.2.2 * D (c2R : Nat)) (a.1 * D (c4R : Nat))

/-- `R`'s `Z` after the accumulator's triple is put in `R`, if it was set. -/
def zFin : Option (Fin pN × Fin pN × Fin pN) → Fe Cv
  | none => 0
  | some a => (2 * a.2.2 : Fin pN)

/-- What the loop in vectors leaves: the fields it only reads, `E`, and the loop's input, as it found them;
`R`'s `Z`, which is that of the accumulator; and `R` is `A` unless that `Z` is zero. -/
structure VFin (c : Joint.Cfg) (base T : Addr) (size u v : Nat) {G : Point Cv} (Q : Point Cv)
    (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) (E : Nat → Fe Cv)
    (acc : Option (Fin pN × Fin pN × Fin pN)) (A : Point Cv) (w : State) : Prop where
  field : Inv c.K.M base size Cv.p (· ∈ nafSlots c.K) (winRo c.K ++ jacCoords c.K.R) (tmv Cv c.K.M.n base w) w
  ro : ∀ x ∈ winRo c.K, tmv Cv c.K.M.n base w x = E x
  z : tmv Cv c.K.M.n base w c.K.R.z = zFin acc
  point : zFin acc ≠ 0 → InvJ Cv (tmv Cv c.K.M.n base w c.K.R.x) (tmv Cv c.K.M.n base w c.K.R.y)
    (tmv Cv c.K.M.n base w c.K.R.z) A
  input : JointWindowInput c Cv base T size u v Q row w

/-- The accumulator's triple into `R`, if it was set: `R` is the accumulator's point, or its `Z` is zero. -/
theorem packR_ok {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {t : State} (hV : VLay c size)
    (hL : JointLayout c size) (hN : Lay c.K.M size (· ∈ nafSlots c.K)) (h : VCore c base T size u v Q row E t)
    {acc : Option (Fin pN × Fin pN × Fin pN)} {A : Point Cv} (hpt : AccPt acc A) (hout : PackSt t acc) :
    WP isa (packR c) t fun w =>
      VFin c base T size u v Q row E acc A w ∧ ProgKeep c.K.M base (jacCoords c.K.R) t w := by
  rw [packR]
  apply WP.seq
  refine WP.mono_syms (test_ok t .rbx) fun a ⟨az, ka⟩ sa => ?_
  have kpa : ProgKeep c.K.M base (jacCoords c.K.R) t a := jointKeeps_prog ka (fun _ hr => absurd hr List.not_mem_nil)
  have ea : tmv Cv c.K.M.n base a = tmv Cv c.K.M.n base t := by funext x; unfold tmv; rw [ka.2.1]
  have fa : Inv c.K.M base size Cv.p (· ∈ nafSlots c.K) (winRo c.K ++ jacCoords c.K.R) (tmv Cv c.K.M.n base a) a := by
    rw [ea]; exact h.field.of_keeps ka (by decide)
  have wa := jwi_work hL h.field.scr h.field.mod.tmp h.input
    (jointKeeps_prog ka (fun _ hr => absurd hr List.not_mem_nil)) sa
  have roa : ∀ x ∈ winRo c.K, tmv Cv c.K.M.n base a x = E x := fun x hx => by rw [ea]; exact h.ro x hx
  cases acc with
  | none =>
    have hb : t.gpr .rbx = 0 := hout
    exact WP.ite true (by show a.zf = _; rw [az, hb]; rfl)
      (fun _ => WP.block_nil ⟨⟨fa, roa, by rw [ea]; exact h.rz, fun hne => absurd rfl hne, wa.1⟩, kpa⟩)
      (fun h => nomatch h)
  | some x =>
    obtain ⟨hb, c3⟩ := hout
    refine WP.ite false (by show a.zf = _; rw [az, hb]; rfl) (fun h => nomatch h) (fun _ => ?_)
    have same : ∀ i, i < 5 → ∀ k, k < 4 → (envOf a).m .rdi (slotOff i) k = (envOf t).m .rdi (slotOff i) k := by
      intro i _ k _
      show (a.mem.readW (a.gpr .rdi + _) 64).toInt = (t.mem.readW (t.gpr .rdi + _) 64).toInt
      rw [ka.2.1, ka.1 .rdi List.not_mem_nil]
    have hSl : ∀ y ∈ jacCoords c.K.R, y ∈ nafSlots c.K := fun y hy => fa.sl y (List.mem_append_right _ hy)
    have mx : c.K.R.x ∈ jacCoords c.K.R := by simp [jacCoords]
    have my : c.K.R.y ∈ jacCoords c.K.R := by simp [jacCoords]
    have mz : c.K.R.z ∈ jacCoords c.K.R := by simp [jacCoords]
    have sub1 {y : Nat} (hy : y ∈ jacCoords c.K.R) : ∀ w ∈ [y], w ∈ jacCoords c.K.R := by
      intro w hw; rw [List.mem_singleton] at hw; subst hw; exact hy
    have sl1 {y : Nat} (hy : y ∈ jacCoords c.K.R) : ∀ w ∈ [y], w ∈ nafSlots c.K := fun w hw => hSl w (sub1 hy w hw)
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono_syms (lane_ok hV hN fa (l := 3) (by decide) mx 4
      (lim_sl5_congr (fun i hi => same i hi 3 (by decide)) c3.x)) fun b1 ⟨k1, i1, v1, s1⟩ y1 => ?_
    rw [WP.block_append_iff]
    refine WP.mono_syms (lane_ok hV hN i1 (l := 0) (by decide) my 4
      (lim_sl5_congr (fun i hi => (s1 i hi 0 (by decide)).trans (same i hi 0 (by decide))) c3.y))
      fun b2 ⟨k2, i2, v2, s2⟩ y2 => ?_
    refine WP.mono_syms (lane_ok hV hN i2 (l := 1) (by decide) mz 2
      (lim_sl5_congr (fun i hi => ((s2 i hi 1 (by decide)).trans (s1 i hi 1 (by decide))).trans
        (same i hi 1 (by decide))) c3.z)) fun b3 ⟨k3, i3, v3, _⟩ y3 => ?_
    have ex : toM Cv.p (2 ^ (64 * c.K.M.n)) (wordsVal b3.mem base c.K.R.x c.K.M.n) = (4 * x.1 : Fin pN) := by
      rw [k3.slot hN i2.scr (sl1 mz) (hSl _ mx) (by rw [List.mem_singleton]; exact hV.rxz),
        k2.slot hN i1.scr (sl1 my) (hSl _ mx) (by rw [List.mem_singleton]; exact hV.rxy), v1]
      rfl
    have ey : toM Cv.p (2 ^ (64 * c.K.M.n)) (wordsVal b3.mem base c.K.R.y c.K.M.n) = (4 * x.2.1 : Fin pN) := by
      rw [k3.slot hN i2.scr (sl1 mz) (hSl _ my) (by rw [List.mem_singleton]; exact hV.ryz), v2]
      rfl
    have ez : toM Cv.p (2 ^ (64 * c.K.M.n)) (wordsVal b3.mem base c.K.R.z c.K.M.n) = (2 * x.2.2 : Fin pN) := v3
    have kr : ProgKeep c.K.M base (jacCoords c.K.R) a b3 :=
      ((k1.mono (sub1 mx)).trans (k2.mono (sub1 my))).trans (k3.mono (sub1 mz))
    have wb := jwi_work hL fa.scr fa.mod.tmp wa.1 (kr.mono (jointWork_R c)) (y3.trans (y2.trans y1))
    refine ⟨⟨i3, fun y hy => (wb.2 y hy).trans (roa y hy), ez, fun hne => ?_, wb.1⟩, kpa.trans kr⟩
    rcases (hpt : Pinv x.1 x.2.1 x.2.2 A) with hz | hJ
    · exact absurd (show (2 * x.2.2 : Fin pN) = 0 by rw [hz]; rfl) hne
    · show InvJ Cv (toM Cv.p _ _) (toM Cv.p _ _) (toM Cv.p _ _) A
      rw [ex, ey, ez]
      exact hJ


/-! ### The loop in vectors, into `R` -/

/-- What the joint multiplication with the loop in vectors keeps. -/
structure VFrame (c : Joint.Cfg) (base : Addr) (s w : State) : Prop where
  gpr : ∀ r, r ∉ Reg.rbx :: clob c.K.M.n → w.gpr r = s.gpr r
  rd : w.rd = s.rd
  wr : w.wr = s.wr
  mem : Unch base (vW ++ ((jacCoords c.K.R).map (·, 8 * c.K.M.n) ++ [(c.K.M.tmp, 8 * c.K.M.n)])) s.mem w.mem

theorem vk_regs {n : Nat} (hn : n = 4) :
    ∀ r ∈ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .rbx], r ∈ Reg.rbx :: clob n := by
  subst hn; decide

theorem car3_congr {s t : State} (h : ∀ i, i < 5 → ∀ k, (envOf t).m .rdi (slotOff i) k = (envOf s).m .rdi (slotOff i) k)
    {a b c : Fin pN} (hc : Car3 (envOf s) sl5 a b c) : Car3 (envOf t) sl5 a b c :=
  ⟨lim_sl5_congr (fun i hi => h i hi _) hc.y, lim_sl5_congr (fun i hi => h i hi _) hc.z,
    lim_sl5_congr (fun i hi => h i hi _) hc.x⟩

/-- What the loop left, with its flag in `rbx`. -/
structure VPack (c : Joint.Cfg) (base T : Addr) (size u v : Nat) {G : Point Cv} (Q : Point Cv)
    (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) (E : Nat → Fe Cv)
    (acc : Option (Fin pN × Fin pN × Fin pN)) (t : State) : Prop where
  core : VCore c base T size u v Q row E t
  pack : PackSt t acc

/-- The loop, with MXCSR saved. -/
theorem vloop_vs {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s : State} (hV : VLay c size)
    (h9 : c.gw = 9) (h : VBase c base T size u v Q row E s) (hx : MxOk s) :
    WP isa (vloop c) s fun t =>
      (VOut c base T size u v Q row E (accN c row (tqE c E) u v 257) t ∧ MxOk t) ∧ WKeep base s t :=
  WP.mono (vloop_ok hV h9 h) fun _ ⟨ot, kt, rt⟩ =>
    let ⟨w, hw⟩ := hx
    ⟨⟨ot, w, rt.trans hw⟩, kt⟩

/-- The loop's flag into `rbx`, and the vectors' upper halves zeroed. -/
theorem vmov_ok {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {s : State} (hV : VLay c size)
    (h : VOut c base T size u v Q row E acc s) (hx : MxOk s) :
    WP isa (.block [.mov .rbx (.reg .r11), .vop .vzeroupper]) s fun t =>
      (VPack c base T size u v Q row E acc t ∧ MxOk t) ∧ WKeep base s t := by
  show WP isa (.block ([.mov .rbx (.reg .r11)] ++ [.vop .vzeroupper])) s _
  rw [WP.block_append_iff]
  refine WP.mono_syms (WP.skeep rfl (mov_ok s .rbx .r11)) fun a ⟨hb, ka⟩ sa => ?_
  refine WP.mono_syms (vzu_ok a) fun t ⟨tg, tm, trd, twr⟩ st => ?_
  have va : VKeep s a := .of_skeep ka
  have ca := h.core.vkeep hV va sa
  have ut : Unch base vW a.mem t.mem := by rw [tm]; exact Unch.refl _ _ _
  have ws := WKeep.of_vkeep h.core.field.scr.rdi va
  refine ⟨⟨⟨ca.unch hV (by rw [tg]) trd twr ut st, ?_⟩, ?_⟩,
    ⟨fun r hr => (congrFun tg r).trans (ws.gpr r hr), trd.trans ka.rd, twr.trans ka.wr, unch_same ws.mem ut⟩⟩
  · have hout := h.out
    have em : ∀ i, i < 5 → ∀ k, (envOf t).m .rdi (slotOff i) k = (envOf s).m .rdi (slotOff i) k := by
      intro i _ k
      refine Eq.trans ?_ (ka.m (b := .rdi) (by decide) _ k)
      show (t.mem.readW (t.gpr .rdi + _) 64).toInt = (a.mem.readW (a.gpr .rdi + _) 64).toInt
      rw [tm, tg]
    cases acc with
    | none => exact ((congrFun tg .rbx).trans hb).trans hout
    | some x => exact ⟨((congrFun tg .rbx).trans hb).trans hout.1, car3_congr em hout.2⟩
  · obtain ⟨w, hw⟩ := hx
    exact ⟨w, ((congrFun tg .r12).trans (ka.gpr .r12 (by decide))).trans hw⟩

/-- The epilogue. -/
theorem mxRestore_vs {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {s : State} (hV : VLay c size)
    (h : VPack c base T size u v Q row E acc s) (hx : MxOk s) :
    WP isa (.block [.store32 (sc MXV) .r12, .ldmxcsr (sc MXV)]) s fun t =>
      VPack c base T size u v Q row E acc t ∧ WKeep base s t := by
  obtain ⟨w, hw⟩ := hx
  have hsb := hV.big
  refine WP.mono_syms (mxRestore_ok h.core.field.scr hV.mx hw) fun t ⟨tm, tg, trd, twr⟩ st => ?_
  have u1 : Unch base [(5864, 4)] s.mem t.mem := by
    rw [tm]; exact unch_write32 (d := MXV) _ base _ (by decide) (by decide) (by decide)
  have ut : Unch base vW s.mem t.mem := u1.cover (by decide)
  have em : ∀ i, i < 5 → ∀ k, k < 4 → (envOf t).m .rdi (slotOff i) k = (envOf s).m .rdi (slotOff i) k := by
    intro i hi k hk
    show (t.mem.readW (t.gpr .rdi + _) 64).toInt = (s.mem.readW (s.gpr .rdi + _) 64).toInt
    rw [tg, h.core.field.scr.rdi]
    congr 1
    apply Mem.readW_congr
    intro j hj
    have hsl : cfg.sbase = 5056 := rfl
    rw [Offset.add_add]
    refine u1 _ fun w hw' => ?_
    rw [List.mem_singleton] at hw'; subst hw'
    rw [ofs_add base (by simp only [slotOff, hsl]; omega)]
    simp only [slotOff, hsl]
    omega
  refine ⟨⟨h.core.unch hV (by rw [tg]) trd twr ut st, ?_⟩, fun r _ => congrFun tg r, trd, twr, ut⟩
  have hp := h.pack
  cases acc with
  | none => exact (by rw [tg] : t.gpr .rbx = s.gpr .rbx).trans hp
  | some x =>
    exact ⟨(by rw [tg] : t.gpr .rbx = s.gpr .rbx).trans hp.1,
      lim_sl5_congr (fun i hi => em i hi 0 (by decide)) hp.2.y, lim_sl5_congr (fun i hi => em i hi 1 (by decide)) hp.2.z,
      lim_sl5_congr (fun i hi => em i hi 3 (by decide)) hp.2.x⟩

/-- The loop over the digits in vectors, from `R = O`: `R` is the accumulator's point, or its `Z` is zero. -/
theorem vmain_vs {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q A : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s : State} (hV : VLay c size)
    (hL : JointLayout c size) (hN : Lay c.K.M size (· ∈ nafSlots c.K)) (h9 : c.gw = 9)
    (h : VBase c base T size u v Q row E s) (hpt : AccPt (accN c row (tqE c E) u v 257) A) :
    WP isa (vmain c) s fun w =>
      VFin c base T size u v Q row E (accN c row (tqE c E) u v 257) A w ∧ VFrame c base s w := by
  rw [vmain, regionAt]
  apply WP.seq
  refine WP.seq (WP.mono (mxSave_vs hV h) fun s₁ ⟨⟨b₁, x₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (mxSet_vs hV b₁ x₁) fun s₂ ⟨⟨b₂, x₂⟩, k₂⟩ => ?_))
  refine WP.seq (WP.seq (WP.mono (vloop_vs hV h9 b₂ x₂) fun s₃ ⟨⟨o₃, x₃⟩, k₃⟩ => ?_))
  refine WP.mono (vmov_ok hV o₃ x₃) fun s₄ ⟨⟨p₄, x₄⟩, k₄⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨s₄, rfl, WP.block_nil ?_⟩
  refine WP.mono (mxRestore_vs hV p₄ x₄) fun s₅ ⟨p₅, k₅⟩ => ?_
  have ks := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  refine WP.mono (packR_ok hV hL hN p₅.core hpt p₅.pack) fun w ⟨fw, kw⟩ => ⟨fw, ?_⟩
  exact ⟨fun r hr => (kw.gpr r (fun h' => hr (List.mem_cons_of_mem _ h'))).trans
    (ks.gpr r (fun h' => hr (vk_regs hV.n r h'))), kw.rd.trans ks.rd, kw.wr.trans ks.wr, ks.mem.trans kw.unch⟩

/-- `Q`'s affine coordinates, among the field elements the loop only reads, are `Q`'s. -/
theorem vcore_affine {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s : State}
    (h : VCore c base T size u v Q row E s) : InvJ Cv (E c.K.P.x) (E c.K.P.y) 1 Q := by
  have hp := h.input.point
  rw [h.input.affine, h.ro _ (by simp [winRo]), h.ro _ (by simp [winRo])] at hp
  exact hp

/-- The loop over the digits in vectors, from `R = O`: `R` is the sum, or its `Z` is zero. -/
theorem vmain_ok (hC : Law Cv) (hO : PrimeOrder Cv) (ha : AM3 Cv) {c : Joint.Cfg} {base T : Addr} {size u v : Nat}
    {G Q : Point Cv} {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv} {s : State}
    (hV : VLay c size) (hL : JointLayout c size) (hN : Lay c.K.M size (· ∈ nafSlots c.K)) (h9 : c.gw = 9)
    (hG : onCurve Cv G = true) (hQ : onCurve Cv Q = true) (h : VBase c base T size u v Q row E s)
    (hu : u < 2 ^ 256) (hv : v < 2 ^ 256) :
    WP isa (vmain c) s fun w =>
      VFin c base T size u v Q row E (accN c row (tqE c E) u v 257) (Spec.Weierstrass.add (mul u G) (mul v Q)) w ∧
        VFrame c base s w := by
  have hpt := accN_pt hC ha row h9 (tabQ_pts hC hO ha hQ (vcore_affine h.core)) hG hQ hu hv 257 (Nat.le_refl _)
  rw [show 257 - 257 = 0 from rfl, jointPoint_zero (gw := 9)] at hpt
  exact vmain_vs hV hL hN h9 h hpt

/-! ### The joint multiplication -/

/-- What the joint multiplication with the loop in vectors writes of the working space. -/
def vRanges (c : Joint.Cfg) : List (Nat × Nat) :=
  (jointInitWork c ++ jointWork c).map (·, 8 * c.K.M.n) ++ [(c.K.M.tmp, 8 * c.K.M.n)] ++ vW

theorem vRanges_sub (c : Joint.Cfg) {W : List Nat} (hW : ∀ x ∈ W, x ∈ jointInitWork c ++ jointWork c) :
    ∀ w ∈ W.map (·, 8 * c.K.M.n) ++ [(c.K.M.tmp, 8 * c.K.M.n)], w ∈ vRanges c := by
  intro w hw
  refine List.mem_append_left _ ?_
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    exact List.mem_append_left _ (List.mem_map_of_mem (hW x hx))
  · exact List.mem_append_right _ hw

/-- `R = O`, for the vectors' code. -/
theorem vseed_ok (hC : Law Cv) {c : Joint.Cfg} {base T : Addr} {size u v : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {s : State} (hL : JointLayout c size)
    (hN : Lay c.K.M size (· ∈ nafSlots c.K)) (hOne : c.K.one < Cv.p)
    (hi : Inv c.K.M base size Cv.p (· ∈ nafSlots c.K) (winRo c.K) (tmv Cv c.K.M.n base s) s)
    (hw : JointWindowInput c Cv base T size u v Q row s) (hT : GTab base T size s) :
    WP isa (.block (Jacobian.infinity c.K c.K.R)) s fun b =>
      VBase c base T size u v Q row (tmv Cv c.K.M.n base s) b ∧ b.rd = s.rd ∧ b.wr = s.wr ∧
        Unch base (vRanges c) s.mem b.mem := by
  have hR : ∀ x ∈ [c.K.R.x, c.K.R.y, c.K.R.z], x ∈ nafSlots c.K := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [nafSlots, winOther, List.mem_append, List.mem_cons]
    rcases hx with rfl | rfl | rfl <;> simp
  refine WP.mono_syms (infinityPoint_ok hN hR hi hOne) fun a ⟨E', ka, ia, pa⟩ sa => ?_
  have kw : ProgKeep c.K.M base (jointWork c) s a := ka.mono (by
    intro x hx
    simp only [rcbW, jointWork, winOther, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    grind)
  have wa := jwi_work hL hi.scr hi.mod.tmp hw kw sa
  have ia' : Inv c.K.M base size Cv.p (· ∈ nafSlots c.K) (winRo c.K ++ jacCoords c.K.R) E' a :=
    ia.sub (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h)
  refine ⟨⟨⟨ia'.to_tmv, wa.2, ?_, wa.1⟩, ⟨by rw [ka.rd, ka.wr]; exact hT.1, hT.2⟩⟩, ka.rd, ka.wr,
    kw.unch.mono (vRanges_sub c fun x hx => List.mem_append_right _ hx)⟩
  exact (ia.val _ (by simp)).trans ((pa.z_zero_iff hC).mpr rfl)

/-- What the joint multiplication leaves for the comparison: `R`'s coordinates, reduced, are `A`'s. -/
structure VRes (c : Joint.Cfg) (base : Addr) (size : Nat) (A : Point Cv) (t : State) : Prop where
  scr : Scr t base size
  x : wordsVal t.mem base c.K.R.x c.K.M.n < Cv.p
  z : wordsVal t.mem base c.K.R.z c.K.M.n < Cv.p
  point : InvJ Cv (tmv Cv c.K.M.n base t c.K.R.x) (tmv Cv c.K.M.n base t c.K.R.y) (tmv Cv c.K.M.n base t c.K.R.z) A

/-- The joint multiplication with the loop in vectors, and `Joint.window` where that leaves `Z` zero:
`R = [u]G + [v]Q`. -/
theorem vwindow_ok (hC : Law Cv) (hO : PrimeOrder Cv) (ha : AM3 Cv) {c : Joint.Cfg} {double : Prog isa}
    {base T : Addr} {size u v : Nat} {G Q : Point Cv} {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)}
    {s : State} (hV : VLay c size) (hL : JointAddLayout c size) (hInit : JointInitLayout c size) (h9 : c.gw = 9)
    (hm : UnitMod Cv.p (2 ^ (64 * c.K.M.n))) (hd : JDblOk Cv c.dbl) (hD : JointDoubler c Cv size double)
    (hOne : c.K.one < Cv.p) (hOneVal : toM Cv.p (2 ^ (64 * c.K.M.n)) c.K.one = 1)
    (hG : onCurve Cv G = true) (hQ : onCurve Cv Q = true) (hZ : c.coZ = true → PrimeOrder Cv ∧ 17 ≤ Cv.n ∧ AM3 Cv)
    (hu : u < 2 ^ (64 * c.K.M.n)) (hv : v < 2 ^ (64 * c.K.M.n))
    (hi : Inv c.K.M base size Cv.p (· ∈ nafSlots c.K) (winRo c.K) (tmv Cv c.K.M.n base s) s)
    (hw : JointWindowInput c Cv base T size u v Q row s) (hT : GTab base T size s) :
    WP isa (vwindow c double).inline s fun t =>
      VRes c base size (Spec.Weierstrass.add (mul u G) (mul v Q)) t ∧ t.gpr .rbx = 0 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Unch base (vRanges c) s.mem t.mem := by
  have hLl := hL.lookup.layout
  have hN := hInit.naf.lay
  have hn := hV.n
  rw [vwindow]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono (vseed_ok hC hLl hN hOne hi hw hT) fun b ⟨hb, rdb, wrb, ub⟩ => ?_
  apply WP.seq
  refine WP.mono (vmain_ok hC hO ha hV hLl hN h9 hG hQ hb (by rw [hn] at hu; exact hu)
    (by rw [hn] at hv; exact hv)) fun d ⟨fd, kd⟩ => ?_
  have ud : Unch base (vRanges c) b.mem d.mem := kd.mem.mono (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact List.mem_append_right _ hw
    · exact vRanges_sub c (fun x hx => List.mem_append_right _ (jointWork_R c x hx)) w hw)
  have mz : c.K.R.z ∈ winRo c.K ++ jacCoords c.K.R := List.mem_append_right _ (by simp [jacCoords])
  have mx : c.K.R.x ∈ winRo c.K ++ jacCoords c.K.R := List.mem_append_right _ (by simp [jacCoords])
  have my : c.K.R.y ∈ winRo c.K ++ jacCoords c.K.R := List.mem_append_right _ (by simp [jacCoords])
  apply WP.seq
  refine WP.mono_syms (zeroField_ok hN hm fd.field mz) fun e ⟨ez, ie, ke⟩ ye => ?_
  have kw : ProgKeep c.K.M base (jointWork c) d e := ke.mono (fun _ h => absurd h List.not_mem_nil)
  have we := jwi_work hLl fd.field.scr fd.field.mod.tmp fd.input kw ye
  have ue : Unch base (vRanges c) d.mem e.mem :=
    kw.unch.mono (vRanges_sub c fun x hx => List.mem_append_right _ hx)
  have rde : e.rd = s.rd := by rw [ke.rd, kd.rd, rdb]
  have wre : e.wr = s.wr := by rw [ke.wr, kd.wr, wrb]
  have use : Unch base (vRanges c) s.mem e.mem := unch_same (unch_same ub ud) ue
  refine WP.ite (decide (tmv Cv c.K.M.n base d c.K.R.z = 0)) ez (fun hz => ?_) (fun hnz => ?_)
  · -- `Z` is zero: the whole of `Joint.window`
    refine WP.mono (jointMulWindow_ok hL hInit hm hC hd hD hOne hOneVal hG hQ hZ hu hv
      (ie.sub (fun x hx => List.mem_append_left _ hx)).to_tmv we.1) fun t ⟨kt, ct, tb⟩ => ?_
    refine ⟨⟨ct.field.scr, ct.field.lt _ (jointLive_R c _ (by simp [jacCoords])),
      ct.field.lt _ (jointLive_R c _ (by simp [jacCoords])), ct.point⟩, tb, by rw [kt.regs.rd, rde],
      by rw [kt.regs.wr, wre], unch_same use (kt.unch.mono (vRanges_sub c fun x hx => hx))⟩
  · -- `Z` is not zero: `R` is the sum
    have hnz' : ¬tmv Cv c.K.M.n base d c.K.R.z = 0 := of_decide_eq_false hnz
    have hp := fd.point (by rw [← fd.z]; exact hnz')
    refine WP.mono (jointCounter_ok e (n := 0) (by decide)) fun t ⟨tb, kt⟩ => ?_
    have tv (y : Nat) (hy : y ∈ winRo c.K ++ jacCoords c.K.R) :
        tmv Cv c.K.M.n base t y = tmv Cv c.K.M.n base d y := by
      unfold tmv; rw [kt.2.1]; exact ie.val y hy
    refine ⟨⟨ie.scr.of_keeps kt (by decide), by rw [kt.2.1]; exact ie.lt _ mx, by rw [kt.2.1]; exact ie.lt _ mz, ?_⟩,
      tb, by rw [kt.2.2.1, rde], by rw [kt.2.2.2, wre], by rw [kt.2.1]; exact use⟩
    rw [tv _ mx, tv _ my, tv _ mz]
    exact hp

end VG.Proof.P256.X86_64.Ifma
