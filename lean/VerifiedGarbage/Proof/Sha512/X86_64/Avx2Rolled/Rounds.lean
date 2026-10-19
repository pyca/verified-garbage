module

public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Compress
public import VerifiedGarbage.Impl.Sha512.X86_64.Avx2Rolled
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# SHA-512 with AVX2 on x86-64, rolled: rounds and schedule steps through the index

`roundR j t'` is round `16 i + t'` of block `j` when `rdx = 128 i` and `rsi`
points at the table of round constants; `scheduleR` stores its words through
the same index. Both are proven once, for any `i`, by relating their
addresses to those of the unrolled code (`Proof/Sha512/X86_64/Avx2/`).
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx2.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2 VG.Impl.Sha512.X86_64.Avx2Rolled
open VG.Proof.Sha512.X86_64.Avx2
open VG.Spec.Sha512 (HashValue Word Block K W)
open VG.Proof.Sha512 (roundKW rounds_succ round_eq)
open VG.Proof.Sha512.X86_64 (ofInt_natCast)

/-! ## Addresses -/

/-- The index of iteration `i`. -/
abbrev idx (i : Nat) : BitVec 64 := BitVec.ofNat 64 (128 * i)

theorem kSlot_ea (s : State) {i : Nat} (h : s.gpr .rdx = idx i) (t' : Nat) :
    s.ea (kSlot t') = s.gpr .rsi + BitVec.ofNat 64 (8 * (16 * i + t')) := by
  simp only [State.ea, kSlot, h, ofInt_natCast, BitVec.mul_one]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 128 * i + 8 * t' = 8 * (16 * i + t') by omega]

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

/-- The table's base register holds its address, and round `n` reads word `n`. -/
theorem exec_kSlot (s : State) (h : Reg) {i : Nat} (t : Nat) (hrdx : s.gpr .rdx = idx i)
    (hb : s.gpr .rsi = s.syms kSym) (hn : 16 * i + t < 80) :
    X86_64.exec (.aluTbl .add h (kSlot t) kSym Spec.Sha512.Ks) s = execAluW .add h (K (16 * i + t)) s := by
  have e : s.ea (kSlot t) - s.syms kSym = BitVec.ofNat 64 (8 * (16 * i + t)) := by
    rw [kSlot_ea s hrdx, hb, BitVec.add_comm, BitVec.add_sub_cancel]
  have e' : (BitVec.ofNat 64 (8 * (16 * i + t))).toNat = 8 * (16 * i + t) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hl : 16 * i + t < Spec.Sha512.Ks.length := by rw [show Spec.Sha512.Ks.length = 80 from rfl]; exact hn
  simp only [X86_64.exec, e, e', show (kSlot t).base = .rsi from rfl, hb, Nat.mul_mod_right,
    Nat.mul_div_right (16 * i + t) (by decide : 0 < 8), hl, and_self, ↓reduceIte]
  rfl

/-- The round is symbolically executed once, for any registers `a … h`. -/
theorem roundR_ok (j t : Nat) (s : State) (v : HashValue) (k w : Word)
    (hv : Vars t s v)
    (hk : X86_64.exec (.aluTbl .add (var t 7) (kSlot t) kSym Spec.Sha512.Ks) s = execAluW .add (var t 7) k s)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (wSlotR j t)) 8)
    (hw : s.mem.readW (s.ea (wSlotR j t)) 64 = w) :
    WP isa (.block (roundR j t)) s fun s' => Vars (t + 1) s' (roundKW v k w) ∧ Keeps s s' := by
  unfold Keeps
  have hd := round_nodup t
  have hd' := VG.nodup_reverse hd
  have eaw : s.ea (wSlotR j t) = s.gpr .rcx + s.gpr .rdx * BitVec.ofNat 64 2 +
      BitVec.ofInt 64 ((32 * (t / 2) + 16 * j + 8 * (t % 2) : Nat) : Int) := rfl
  rw [eaw] at hin hw
  apply WP.of_runBlock
  rw [show roundR j t = .aluTbl .add (var t 7) (kSlot t) kSym Spec.Sha512.Ks :: (roundR j t).tail from rfl,
    runBlock_cons, hk]
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega),
    var_succ t _ (show 1 < 7 by omega), var_succ t _ (show 2 < 7 by omega),
    var_succ t _ (show 3 < 7 by omega), var_succ t _ (show 4 < 7 by omega),
    var_succ t _ (show 5 < 7 by omega), var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hc⟩ := hv
  simp only [roundR, wSlotR, List.tail_cons]
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
    runBlock_nil, exec, execAlu, execAluW, execRorx, execAndn, readSrc, State.ea,
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
      List.getElem_cons_succ, maj_carry, bsig0_rorx, t1_order, and_self]
    exact ⟨BitVec.add_assoc _ _ _, trivial⟩

/-- Round `16 i + t'` can read `K`: the table is at `kb`, the address of the static. -/
def KOk (kb : Addr) (s : State) (t : Nat) : Prop := s.syms kSym = kb ∧ t < 80

theorem KOk.keeps {kb : Addr} {s s' : State} {t : Nat} (h : KOk kb s t) (hk : KeepsS s s') : KOk kb s' t := by
  rw [KOk, hk.2]; exact h

theorem KOk.of_syms {kb : Addr} {s s' : State} {t : Nat} (h : KOk kb s t) (hs : s'.syms = s.syms) :
    KOk kb s' t := by
  rw [KOk, hs]; exact h

/-- What iteration `i` of a loop of rounds needs of its state. -/
structure Idx (kb : Addr) (i : Nat) (s : State) : Prop where
  rdx : s.gpr .rdx = idx i
  rsi : s.gpr .rsi = kb

theorem Idx.keeps {kb : Addr} {i : Nat} {s s' : State} (h : Idx kb i s) (hk : KeepsS s s') : Idx kb i s' :=
  ⟨(hk.1.2.2.2.1 .rdx (by decide)).trans h.rdx, (hk.1.2.2.2.1 .rsi (by decide)).trans h.rsi⟩

theorem roundR_step (j i t : Nat) (H : HashValue) (M : Block) (s : State) {kb : Addr} (hI : Idx kb i s)
    (hv : Vars t s (Spec.Sha512.rounds H M (16 * i + t))) (hk : KOk kb s (16 * i + t))
    (hw : WOk j M s (16 * i + t)) :
    WP isa (.block (roundR j t)) s fun s' =>
      Vars (t + 1) s' (Spec.Sha512.rounds H M (16 * i + t + 1)) ∧ KeepsS s s' := by
  rw [rounds_succ, round_eq]
  have ew := wSlotR_ea s hI.rdx j t
  exact VG.X86_64.WP.mono_syms (roundR_ok j t s _ _ _ hv (exec_kSlot s _ t hI.rdx (hI.rsi.trans hk.1.symm) hk.2)
    (by rw [ew]; exact hw.1) (by rw [ew]; exact hw.2)) fun _ ⟨hv', hk'⟩ hs => ⟨hv', hk', hs⟩

/-- `n ≤ 16` rounds of block `j` in iteration `i`, after `p`. -/
theorem roundsR_ok (j i : Nat) (H : HashValue) (M : Block) {kb : Addr} {p : Prog isa} {s : State}
    {P : State → Prop}
    (hp : WP isa p s fun s' => P s' ∧ Vars 0 s' (Spec.Sha512.rounds H M (16 * i)) ∧ Keeps s s')
    (hI : Idx kb i s) (hk : ∀ t < 16, KOk kb s (16 * i + t)) (hw : ∀ t < 16, WOk j M s (16 * i + t)) :
    ∀ n ≤ 16, WP isa (roundsR j p n) s fun s' =>
      (∃ s₁, P s₁ ∧ KeepsS s₁ s') ∧ Vars n s' (Spec.Sha512.rounds H M (16 * i + n)) ∧ KeepsS s s' := by
  intro n hn
  induction n with
  | zero =>
    exact VG.X86_64.WP.mono_syms hp fun s' ⟨hP, hv, hk'⟩ hs => ⟨⟨s', hP, KeepsS.refl _⟩, hv, hk', hs⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ ⟨hP₁, hv₁, hk₁⟩ => ?_)
    refine WP.mono (roundR_step j i n H M s₁ (hI.keeps hk₁) hv₁ ((hk n (by omega)).keeps hk₁)
      ((hw n (by omega)).keeps hk₁.1)) fun s₂ ⟨hv₂, hk₂⟩ => ?_
    obtain ⟨s₀, hP₀, hk₀⟩ := hP₁
    exact ⟨⟨s₀, hP₀, hk₀.trans hk₂⟩, hv₂, hk₁.trans hk₂⟩

/-! ## The schedule, through the index -/

theorem scheduleR_eq (i : Nat) :
    scheduleR i = (schedule i).dropLast ++ ([.vmovdquStore .l256 (sSlot i) (msg i)] : List Instr) := rfl

/-- `schedule_ok`, storing through the index. -/
theorem scheduleR_ok (n : Nat) (s : State) (a b c d e a' b' c' d' e' : BitVec 128)
    (ha : s.xmm (msg n) = a) (hb : s.xmm (msg (n + 1)) = b) (hc : s.xmm (msg (n + 4)) = c)
    (hd : s.xmm (msg (n + 5)) = d) (he : s.xmm (msg (n + 7)) = e)
    (ha' : s.ymmHi (msg n) = a') (hb' : s.ymmHi (msg (n + 1)) = b') (hc' : s.ymmHi (msg (n + 4)) = c')
    (hd' : s.ymmHi (msg (n + 5)) = d') (he' : s.ymmHi (msg (n + 7)) = e')
    (hout : InRegions s.wr (s.ea (sSlot n)) 32) :
    WP isa (.block (scheduleR n)) s fun s' =>
      s'.xmm (msg n) = xupd a b c d e ∧ s'.ymmHi (msg n) = xupd a' b' c' d' e' ∧
      (∀ r, r ≠ msg n → r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ t3 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (s.ea (sSlot n)) (xupd a' b' c' d' e' ++ xupd a b c d e) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := msg_nodup n
  have hn' := VG.nodup_reverse hn
  have eas : s.ea (sSlot n) = s.gpr .rcx + s.gpr .rdx * BitVec.ofNat 64 2 +
      BitVec.ofInt 64 ((32 * n : Nat) : Int) := rfl
  rw [eas] at hout ⊢
  apply WP.of_runBlock
  simp only [scheduleR, schedule, vb, vs, List.dropLast, List.cons_append, List.nil_append, sSlot]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 4) = x₄ at *
  generalize msg (n + 5) = x₅ at *
  generalize msg (n + 7) = x₇ at *
  simp only [t0, t1, t2, t3, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hn hn' ⊢
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, and_self, runBlock_cons, runStep_some, runBlock_nil, exec,
    VOp.exec, isa, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, State.lane, State.ymm, State.store256, State.ea, hout, hn, hn',
    ha, hb, hc, hd, he, ha', hb', hc', hd', he', Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h0 h1 h2 h3 h4 => by simp [h0, h1, h2, h3, h4], trivial, rfl, trivial⟩

end VG.Proof.Sha512.X86_64.Avx2.Rolled
