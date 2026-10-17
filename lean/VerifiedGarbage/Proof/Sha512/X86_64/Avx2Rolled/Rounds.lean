module

public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Compress
public import VerifiedGarbage.Impl.Sha512.X86_64.Avx2Rolled
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SHA-512 with AVX2 on x86-64, rolled: rounds and schedule steps through the index

`roundR j t'` is round `16 i + t'` of block `j` when `rdx = 128 i`, reading
`Wₜ + Kₜ`; `scheduleR` stores its words plus their constants, from the table
at `rsi`, through the same index. Both are proven once, for any `i`, by relating their
addresses to those of the unrolled code (`Proof/Sha512/X86_64/Avx2/`).
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx2.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2 VG.Impl.Sha512.X86_64.Avx2Rolled
open VG.Proof.Sha512.X86_64.Avx2
open VG.Spec.Sha512 (HashValue Word Block K W bsig1 ch)
open VG.Proof.Sha512 (roundKW rounds_succ round_eq)
open VG.Proof.Sha512.X86_64 (ofInt_natCast)

/-! ## Addresses -/

/-- The index of iteration `i`. -/
abbrev idx (i : Nat) : BitVec 64 := BitVec.ofNat 64 (128 * i)

theorem kSlot_ea (s : State) {i : Nat} (h : s.gpr .rdx = idx i) (n : Nat) :
    s.ea (kSlot n) = s.gpr .rsi + BitVec.ofNat 64 (32 * (8 * i + n)) := by
  simp only [State.ea, kSlot, h, ofInt_natCast]
  rw [BitVec.ofNat_mul_ofNat, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 128 * i * 2 + 32 * n = 32 * (8 * i + n) by omega]

theorem wSlotR_ea (s : State) {i : Nat} (h : s.gpr .rdx = idx i) (j t' : Nat) :
    s.ea (wSlotR j t') = s.ea (wSlot j (16 * i + t')) := by
  simp only [State.ea, wSlotR, wSlot, at_, h, ofInt_natCast]
  rw [BitVec.ofNat_mul_ofNat, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 128 * i * 2 + (32 * (t' / 2) + 16 * j + 8 * (t' % 2)) =
      32 * ((16 * i + t') / 2) + 16 * j + 8 * ((16 * i + t') % 2) by omega]

theorem sSlot_ea (s : State) {i : Nat} (h : s.gpr .rdx = idx i) (n : Nat) :
    s.ea (sSlot n) = wAddr (s.gpr .rcx) (8 * i + n) := by
  simp only [State.ea, sSlot, h, wAddr, ofInt_natCast]
  rw [BitVec.ofNat_mul_ofNat, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 128 * i * 2 + 32 * n = 32 * (8 * i + n) by omega]

/-! ## Rounds -/

theorem var_add16 (i t k : Nat) :
    Impl.Sha512.X86_64.Avx2.var (16 * i + t) k = Impl.Sha512.X86_64.Avx2.var t k := by
  simp only [Impl.Sha512.X86_64.Avx2.var]; congr 1; omega

theorem carry_add16 (i t : Nat) : carry (16 * i + t) = carry t := by
  simp only [carry]; rw [show (16 * i + t) % 2 = t % 2 by omega]

theorem vars_add16 (i t : Nat) (s : State) (v : HashValue) : Vars (16 * i + t) s v ↔ Vars t s v := by
  simp only [Vars, var_add16, carry_add16]

/-- `Keeps`, and the addresses of the statics. -/
def KeepsS (s s' : State) : Prop := Keeps s s' ∧ s'.syms = s.syms

theorem KeepsS.refl (s : State) : KeepsS s s := ⟨Keeps.refl s, rfl⟩

theorem KeepsS.trans {s₁ s₂ s₃ : State} (h₁ : KeepsS s₁ s₂) (h₂ : KeepsS s₂ s₃) : KeepsS s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-! ## The table -/

/-- The constants of words `2p` and `2p+1`, in both lanes of the table. -/
def kpair (p : Nat) : BitVec 128 := K (2 * p + 1) ++ K (2 * p)

/-- Words `2p` and `2p+1` of `M`'s schedule, plus their constants. -/
def pairK (M : Block) (p : Nat) : BitVec 128 := XBinOp.eval .paddq (pair M p) (kpair p)

theorem qword_pairK (M : Block) (p : Nat) {q : Nat} (hq : q < 2) :
    qword (pairK M p) q = W M (2 * p + q) + K (2 * p + q) := by
  rw [pairK, pair, kpair, paddq_eq]
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
  · exact qword_append_0 _ _
  · exact qword_append_1 _ _

theorem ks2_getD {p q : Nat} (hp : p < 40) (hq : q < 4) : ks2.getD (4 * p + q) 0 = K (2 * p + q % 2) := by
  simp only [ks2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show 4 * p + q < 160 by omega),
    Option.map_some, Option.getD_some]
  congr 1; omega

theorem ks2_length : ks2.length = 160 := by simp [ks2]

/-- `vmovdquTbl` of the constants of words `2p` and `2p+1`, from a base
register holding the table's address. -/
theorem exec_tbl (s : State) (r : XReg) (m : MemOp) {p : Nat} (hp : p < 40)
    (hb : s.gpr m.base = s.syms kSym) (ho : s.ea m = s.gpr m.base + BitVec.ofNat 64 (32 * p)) :
    X86_64.exec (.vmovdquTbl r m kSym ks2) s = some (s.setV .l256 r (kpair p) (kpair p)) := by
  have e : (s.ea m - s.syms kSym).toNat = 32 * p := by
    rw [ho, hb, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [X86_64.exec, hb, e, ks2_length, show 32 * p % 8 = 0 by omega, show 32 * p / 8 + 4 ≤ 160 by omega,
    and_self, ↓reduceIte]
  rw [show 32 * p / 8 = 4 * p by omega, ks2_getD hp (q := 0) (by decide), ks2_getD hp (q := 1) (by decide),
    ks2_getD hp (q := 2) (by decide), ks2_getD hp (q := 3) (by decide)]
  rfl

/-- Adding the constants to `x`'s words and storing them, as `scheduleR` and
`loadR` end. -/
theorem addK_ok (r x : XReg) (hrx : x ≠ r) (m₁ m₂ : MemOp) (s : State) (kp : BitVec 128)
    (hk : X86_64.exec (.vmovdquTbl r m₁ kSym ks2) s = some (s.setV .l256 r kp kp))
    (hout : InRegions s.wr (s.ea m₂) 32) :
    WP isa (.block [.vmovdquTbl r m₁ kSym ks2, vb .vpaddq r x r, .vmovdquStore .l256 m₂ r]) s fun s' =>
      s'.mem = s.mem.writeW (s.ea m₂)
        (XBinOp.eval .paddq (s.ymmHi x) kp ++ XBinOp.eval .paddq (s.xmm x) kp) ∧
      (∀ q, q ≠ r → s'.xmm q = s.xmm q ∧ s'.ymmHi q = s.ymmHi q) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms := by
  simp only [State.ea] at hout
  apply WP.of_runBlock
  rw [runBlock_cons, hk]
  simp only [vb, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    isa, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, State.lane, State.ymm, State.store256, State.ea, hrx, hout,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun q hq => by simp [hq], trivial, trivial, trivial, rfl⟩

/-! ## Rounds, reading `Wₜ + Kₜ` -/

/-- `T₁` in the order `roundR` adds it up. -/
theorem t1_orderK (h e f g k w : Word) :
    h + (w + k) + ((e &&& f) + (~~~e &&& g)) +
        (e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41) =
      h + bsig1 e + ch e f g + k + w := by
  rw [ch_add, bsig1_rorx]; ac_rfl

/-- The round is symbolically executed once, for any registers `a … h`. -/
theorem roundR_ok (j t : Nat) (s : State) (v : HashValue) (k w : Word)
    (hv : Vars t s v)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (wSlotR j t)) 8)
    (hw : s.mem.readW (s.ea (wSlotR j t)) 64 = w + k) :
    WP isa (.block (roundR j t)) s fun s' => Vars (t + 1) s' (roundKW v k w) ∧ Keeps s s' := by
  unfold Keeps
  have hd := round_nodup t
  have hd' := VG.nodup_reverse hd
  have eaw : s.ea (wSlotR j t) = s.gpr .rcx + s.gpr .rdx * BitVec.ofNat 64 2 +
      BitVec.ofInt 64 ((32 * (t / 2) + 16 * j + 8 * (t % 2) : Nat) : Int) := rfl
  rw [eaw] at hin hw
  apply WP.of_runBlock
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega),
    var_succ t _ (show 1 < 7 by omega), var_succ t _ (show 2 < 7 by omega),
    var_succ t _ (show 3 < 7 by omega), var_succ t _ (show 4 < 7 by omega),
    var_succ t _ (show 5 < 7 by omega), var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hc⟩ := hv
  simp only [roundR, wSlotR]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  generalize carry t = x at *
  generalize carry (t + 1) = y at *
  simp only [T, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hd hd' ⊢
  simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reducePow, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, execRorx, execAndn, readSrc, State.ea,
    isa, State.load64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.xmm_setReg, RegUpd.ymmHi_setReg, arithFlags, RegUpd.gpr_setFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.xmm_setFlags,
    RegUpd.ymmHi_setFlags,
    hd, hd', h0, h1, h2, h3, h4, h5, h6, h7, hc, hin, hw, and_self, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  rotate_left
  · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hd']
  · simp only [roundKW, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, maj_carry, bsig0_rorx, t1_orderK, and_self]
    exact ⟨BitVec.add_assoc _ _ _, trivial⟩

/-- Round `t` of block `j` can read `Wₜ + Kₜ` of `M`. -/
def WKOk (j : Nat) (M : Block) (s : State) (t : Nat) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 8 ∧ s.mem.readW (s.ea (wSlot j t)) 64 = W M t + K t

theorem WKOk.keeps {j : Nat} {M : Block} {s s' : State} {t : Nat} (h : WKOk j M s t) (hk : Keeps s s') :
    WKOk j M s' t := by
  have e : s'.ea (wSlot j t) = s.ea (wSlot j t) := by
    simp only [State.ea, wSlot, at_, hk.2.2.2.1 .rcx (by decide)]
  rw [WKOk, e, hk.1, hk.2.1, hk.2.2.1]; exact h

theorem roundR_step (j i t : Nat) (H : HashValue) (M : Block) (s : State) (hI : s.gpr .rdx = idx i)
    (hv : Vars t s (Spec.Sha512.rounds H M (16 * i + t))) (hw : WKOk j M s (16 * i + t)) :
    WP isa (.block (roundR j t)) s fun s' =>
      Vars (t + 1) s' (Spec.Sha512.rounds H M (16 * i + t + 1)) ∧ KeepsS s s' := by
  rw [rounds_succ, round_eq]
  have ew := wSlotR_ea s hI j t
  exact VG.X86_64.WP.mono_syms (roundR_ok j t s _ _ _ hv (by rw [ew]; exact hw.1) (by rw [ew]; exact hw.2))
    fun _ ⟨hv', hk'⟩ hs => ⟨hv', hk', hs⟩

/-- `n ≤ 16` rounds of block `j` in iteration `i`, after `p`. -/
theorem roundsR_ok (j i : Nat) (H : HashValue) (M : Block) {p : Prog isa} {s : State}
    {P : State → Prop}
    (hp : WP isa p s fun s' => P s' ∧ Vars 0 s' (Spec.Sha512.rounds H M (16 * i)) ∧ Keeps s s')
    (hI : s.gpr .rdx = idx i) (hw : ∀ t < 16, WKOk j M s (16 * i + t)) :
    ∀ n ≤ 16, WP isa (roundsR j p n) s fun s' =>
      (∃ s₁, P s₁ ∧ KeepsS s₁ s') ∧ Vars n s' (Spec.Sha512.rounds H M (16 * i + n)) ∧ KeepsS s s' := by
  intro n hn
  induction n with
  | zero =>
    exact VG.X86_64.WP.mono_syms hp fun s' ⟨hP, hv, hk'⟩ hs => ⟨⟨s', hP, KeepsS.refl _⟩, hv, hk', hs⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ ⟨hP₁, hv₁, hk₁⟩ => ?_)
    refine WP.mono (roundR_step j i n H M s₁ ((hk₁.1.2.2.2.1 .rdx (by decide)).trans hI) hv₁
      ((hw n (by omega)).keeps hk₁.1)) fun s₂ ⟨hv₂, hk₂⟩ => ?_
    obtain ⟨s₀, hP₀, hk₀⟩ := hP₁
    exact ⟨⟨s₀, hP₀, hk₀.trans hk₂⟩, hv₂, hk₁.trans hk₂⟩

/-! ## The schedule, through the index -/

theorem scheduleR_eq (i : Nat) :
    scheduleR i = (schedule i).dropLast ++
      ([.vmovdquTbl t2 (kSlot i) kSym ks2, vb .vpaddq t2 (msg i) t2, .vmovdquStore .l256 (sSlot i) t2] :
        List Instr) := rfl

theorem syms_setV (s : State) (l : VLen) (r : XReg) (lo hi : BitVec 128) : (s.setV l r lo hi).syms = s.syms := rfl

theorem msg_ne_t (n : Nat) : msg n ≠ t0 ∧ msg n ≠ t2 := by
  have key : ∀ c < 8, msg c ≠ t0 ∧ msg c ≠ t2 := by decide
  rw [show msg n = msg (n % 8) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide))

/-- `schedule_ok`, without the store. -/
theorem scheduleD_ok (n : Nat) (s : State) (a b c d e a' b' c' d' e' : BitVec 128)
    (ha : s.xmm (msg n) = a) (hb : s.xmm (msg (n + 1)) = b) (hc : s.xmm (msg (n + 4)) = c)
    (hd : s.xmm (msg (n + 5)) = d) (he : s.xmm (msg (n + 7)) = e)
    (ha' : s.ymmHi (msg n) = a') (hb' : s.ymmHi (msg (n + 1)) = b') (hc' : s.ymmHi (msg (n + 4)) = c')
    (hd' : s.ymmHi (msg (n + 5)) = d') (he' : s.ymmHi (msg (n + 7)) = e') :
    WP isa (.block (schedule n).dropLast) s fun s' =>
      s'.xmm (msg n) = xupd a b c d e ∧ s'.ymmHi (msg n) = xupd a' b' c' d' e' ∧
      (∀ r, r ≠ msg n → r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ t3 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms := by
  have hn := msg_nodup n
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [schedule, vb, vs, List.dropLast]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 4) = x₄ at *
  generalize msg (n + 5) = x₅ at *
  generalize msg (n + 7) = x₇ at *
  simp only [t0, t1, t2, t3, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hn hn' ⊢
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    VOp.exec, isa, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, syms_setV, State.lane, hn, hn',
    ha, hb, hc, hd, he, ha', hb', hc', hd', he', Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, fun r h0 h1 h2 h3 h4 => by simp [h0, h1, h2, h3, h4], trivial, trivial, trivial, trivial, trivial⟩

/-- `schedule_ok`, storing the words plus their constants through the index. -/
theorem scheduleR_ok (n : Nat) (s : State) (a b c d e a' b' c' d' e' : BitVec 128) {i p : Nat}
    (hp : p < 40) (hI : s.gpr .rdx = idx i) (hip : 8 * i + n = p) (hkb : s.gpr .rsi = s.syms kSym)
    (ha : s.xmm (msg n) = a) (hb : s.xmm (msg (n + 1)) = b) (hc : s.xmm (msg (n + 4)) = c)
    (hd : s.xmm (msg (n + 5)) = d) (he : s.xmm (msg (n + 7)) = e)
    (ha' : s.ymmHi (msg n) = a') (hb' : s.ymmHi (msg (n + 1)) = b') (hc' : s.ymmHi (msg (n + 4)) = c')
    (hd' : s.ymmHi (msg (n + 5)) = d') (he' : s.ymmHi (msg (n + 7)) = e')
    (hout : InRegions s.wr (s.ea (sSlot n)) 32) :
    WP isa (.block (scheduleR n)) s fun s' =>
      s'.xmm (msg n) = xupd a b c d e ∧ s'.ymmHi (msg n) = xupd a' b' c' d' e' ∧
      (∀ r, r ≠ msg n → r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ t3 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (s.ea (sSlot n))
        (XBinOp.eval .paddq (xupd a' b' c' d' e') (kpair p) ++ XBinOp.eval .paddq (xupd a b c d e) (kpair p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms := by
  rw [scheduleR_eq, WP.block_append_iff]
  refine WP.mono (scheduleD_ok n s a b c d e a' b' c' d' e' ha hb hc hd he ha' hb' hc' hd' he')
    fun s₁ ⟨x₁, y₁, o₁, g₁, m₁, rd₁, wr₁, sy₁⟩ => ?_
  have ho : s₁.ea (kSlot n) = s₁.gpr (kSlot n).base + BitVec.ofNat 64 (32 * p) := by
    rw [kSlot_ea s₁ (by rw [g₁]; exact hI), hip]; rfl
  have hs₁ : s₁.ea (sSlot n) = s.ea (sSlot n) := by simp only [State.ea, sSlot, g₁]
  refine VG.X86_64.WP.mono_syms (addK_ok t2 (msg n) (msg_ne_t n).2 (kSlot n) (sSlot n) s₁ (kpair p)
    (exec_tbl s₁ t2 (kSlot n) hp (by rw [sy₁, show (kSlot n).base = .rsi from rfl, g₁]; exact hkb) ho)
    (by rw [hs₁, wr₁]; exact hout)) fun s₂ ⟨m₂, o₂, g₂, rd₂, wr₂, sy₂⟩ _ => ?_
  refine ⟨by rw [(o₂ _ (msg_ne_t n).2).1]; exact x₁, by rw [(o₂ _ (msg_ne_t n).2).2]; exact y₁,
    fun r h0 h1 h2 h3 h4 => ?_, g₂.trans g₁, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sy₂.trans sy₁⟩
  · rw [(o₂ r h3).1, (o₂ r h3).2]; exact o₁ r h0 h1 h2 h3 h4
  · rw [m₂, hs₁, m₁, x₁, y₁]

end VG.Proof.Sha512.X86_64.Avx2.Rolled
