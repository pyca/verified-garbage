import VerifiedGarbage.Proof.Scrypt.X86_64.Salsa
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMixFused

/-! The scalar BlockMix state retained between Salsa invocations. -/
namespace VG.Proof.Scrypt.X86_64.Retained
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (Word)

structure Words (p : Addr) (v : Vector Word 16) (s : State) : Prop where
  regs : ∀ k (hk : k < 12), s.gpr (wreg k) = (v[k]'(by omega)).setWidth 64
  slots : ∀ k (hk : k < 16), 12 ≤ k → s.mem.readW (bufAt p (slotOff k)) 32 = (v[k]'(by omega))
  rsi : s.gpr .rsi = p

theorem Words.rounds {p : Addr} {v : Vector Word 16} {s : State} (h : Words p v s)
    (hw : scR p ∈ s.wr) (n : Nat) :
    WP isa (rounds n) s fun t => Words p (Nat.repeat Spec.Scrypt.doubleRound n v) t ∧
      Frame [slotR p] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsp = s.gpr .rsp := by
  have hi : RI p v s s := ⟨h.regs, h.slots, Frame.refl _ _, rfl, rfl, h.rsi, rfl, rfl⟩
  exact WP.mono (rounds_ok hi hw n) fun _ h => ⟨⟨h.regs, h.slots, h.rsi⟩, h.frame, h.rd, h.wr, h.rdi, h.rsp⟩

theorem Words.reg {p : Addr} {v : Vector Word 16} {s t : State} (h : Words p v s)
    {k : Nat} (hk : k < 12) {x : Word} (u : Upd (wreg k) (x.setWidth 64) s t) :
    Words p (v.set k x) t := by
  refine ⟨fun j hj => ?_, fun j hj h12 => ?_, (u.other _ (wreg_ne k hk).2.1.symm).trans h.rsi⟩
  · simp only [Vector.getElem_set]
    by_cases e : k = j
    · subst j; simp only [ite_true, u.gpr]
    · rw [ite_eq_right e, u.other _ (fun e' => e (wreg_inj k hk j hj e'.symm)), h.regs j hj]
  · rw [Vector.getElem_set, ite_eq_right (by omega), u.mem]; exact h.slots j hj h12

theorem Words.store {p a : Addr} {v : Vector Word 16} {s : State} (h : Words p v s)
    {x : Word} (hd : (slotR p).Disjoint ⟨a, 4⟩) :
    Words p v {s with mem := s.mem.writeW a x} := by
  refine ⟨h.regs, fun k hk h12 => ?_, h.rsi⟩
  rw [Mem.readW_writeW_sep (hd.sep (contains_off (by simp only [slotOff]; omega)
    (by simp only [slotOff]; omega)) (Region.contains_self _ _)) (by decide)]
  exact h.slots k hk h12

theorem xor_reg {p : Addr} {v : Vector Word 16} {s : State} (h : Words p v s)
    {k : Nat} (hk : k < 12) {x : Word}
    (hr : readSrc32 s (.mem (at_ .rax (4 * k))) = some x)
    (hw : InRegions s.wr (s.ea (at_ .rdi (4 * k))) 4)
    (hd : (slotR p).Disjoint ⟨s.ea (at_ .rdi (4 * k)), 4⟩) :
    WP isa (.block (fusedXorWord k)) s fun t =>
      Words p (v.set k ((v[k]'(by omega)) ^^^ x)) t ∧
      t.mem = s.mem.writeW (s.ea (at_ .rdi (4 * k))) ((v[k]'(by omega)) ^^^ x) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ wreg k → t.gpr r = s.gpr r) := by
  rw [fusedXorWord, ite_eq_left hk]
  refine wp_cons (xor32_upd (d := wreg k) hr) fun t u => ?_
  have val : t.gpr (wreg k) = ((v[k]'(by omega)) ^^^ x).setWidth 64 := by
    rw [u.gpr, h.regs k hk]; simp
  have hu : Upd (wreg k) (((v[k]'(by omega)) ^^^ x).setWidth 64) s t := {u with gpr := val}
  have ea : t.ea (at_ .rdi (4 * k)) = s.ea (at_ .rdi (4 * k)) := by
    rw [ea_at, ea_at, u.other _ (wreg_ne k hk).2.2.1.symm]
  refine WP.block_cons_iff.mpr ⟨_, store32_exec (by rw [ea, u.wr]; exact hw), WP.block_nil ?_⟩
  have val32 : (t.gpr (wreg k)).setWidth 32 = (v[k]'(by omega)) ^^^ x := by rw [val]; simp
  rw [ea, val32]
  exact ⟨(h.reg hk hu).store hd, by rw [u.mem], u.rd, u.wr, u.other⟩
theorem finish_reg {p : Addr} {v : Vector Word 16} {s : State} (h : Words p v s)
    {k : Nat} (hk : k < 12) {x : Word}
    (hr : readSrc32 s (.mem (at_ .rdi (4 * k))) = some x)
    (hw : InRegions s.wr (s.ea (at_ .rdi (4 * k))) 4)
    (hd : (slotR p).Disjoint ⟨s.ea (at_ .rdi (4 * k)), 4⟩) :
    WP isa (.block (fusedFinishWord k)) s fun t =>
      Words p (v.set k ((v[k]'(by omega)) + x)) t ∧
      t.mem = s.mem.writeW (s.ea (at_ .rdi (4 * k))) ((v[k]'(by omega)) + x) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ wreg k → t.gpr r = s.gpr r) := by
  rw [fusedFinishWord, finishWord, ite_eq_left hk, ite_eq_left hk, List.append_nil]
  refine wp_cons (add32_upd (d := wreg k) hr) fun t u => ?_
  have val : t.gpr (wreg k) = ((v[k]'(by omega)) + x).setWidth 64 := by
    rw [u.gpr, h.regs k hk]; simp
  have hu : Upd (wreg k) (((v[k]'(by omega)) + x).setWidth 64) s t := {u with gpr := val}
  have ea : t.ea (at_ .rdi (4 * k)) = s.ea (at_ .rdi (4 * k)) := by
    rw [ea_at, ea_at, u.other _ (wreg_ne k hk).2.2.1.symm]
  refine WP.block_cons_iff.mpr ⟨_, store32_exec (by rw [ea, u.wr]; exact hw), WP.block_nil ?_⟩
  have val32 : (t.gpr (wreg k)).setWidth 32 = (v[k]'(by omega)) + x := by rw [val]; simp
  rw [ea, val32]
  exact ⟨(h.reg hk hu).store hd, by rw [u.mem], u.rd, u.wr, u.other⟩


theorem Words.rax {p : Addr} {v : Vector Word 16} {s t : State} (h : Words p v s)
    {x : BitVec 64} (u : Upd .rax x s t) : Words p v t :=
  ⟨fun k hk => (u.other _ (wreg_ne k hk).1).trans (h.regs k hk),
    fun k hk h12 => u.mem ▸ h.slots k hk h12, (u.other _ (by decide)).trans h.rsi⟩

theorem Words.slot {p : Addr} {v : Vector Word 16} {s : State} (h : Words p v s)
    {k : Nat} (hk : k < 16) (h12 : 12 ≤ k) (x : Word) :
    Words p (v.set k x) {s with mem := s.mem.writeW (bufAt p (slotOff k)) x} := by
  refine ⟨fun j hj => ?_, fun j hj hj12 => ?_, h.rsi⟩
  · rw [Vector.getElem_set, ite_eq_right (by omega)]; exact h.regs j hj
  · by_cases e : k = j
    · subst j; rw [Vector.getElem_set, ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
    · rw [Vector.getElem_set, ite_eq_right e]
      rw [readW_writeW_off _ _ _ (by omega) (by simp only [slotOff]; omega)
        (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)]
      exact h.slots j hj hj12

theorem finish_slot {p : Addr} {v : Vector Word 16} {s : State} (h : Words p v s)
    {k : Nat} (hk : k < 16) (h12 : 12 ≤ k) {x : Word}
    (hr : readSrc32 s (.mem (at_ .rdi (4 * k))) = some x)
    (hs : InRegions s.wr (bufAt p (slotOff k)) 4)
    (hw : InRegions s.wr (s.ea (at_ .rdi (4 * k))) 4)
    (hd : (slotR p).Disjoint ⟨s.ea (at_ .rdi (4 * k)), 4⟩) :
    WP isa (.block (fusedFinishWord k)) s fun t =>
      Words p (v.set k ((v[k]'(by omega)) + x)) t ∧
      t.mem = (s.mem.writeW (s.ea (at_ .rdi (4 * k))) ((v[k]'(by omega)) + x)).writeW
        (bufAt p (slotOff k)) ((v[k]'(by omega)) + x) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) := by
  rw [fusedFinishWord, finishWord, ite_eq_right (by omega), ite_eq_right (by omega)]
  have read : readSrc32 s (.mem (at_ .rsi (slotOff k))) = some (v[k]'hk) := by
    simp only [readSrc32, ea_at, h.rsi, State.load32,
      VG.Proof.Scrypt.Memory.InRegions.right hs, ite_true, h.slots k hk h12]
  refine wp_cons (mov32_upd (d := .rax) read) fun a ua => ?_
  have hb : readSrc32 a (.mem (at_ .rdi (4 * k))) = some x := by
    have hin := VG.Proof.Scrypt.Memory.InRegions.right (rd := s.rd) hw
    have he : a.ea (at_ .rdi (4 * k)) = s.ea (at_ .rdi (4 * k)) := by
      rw [ea_at, ea_at, ua.other _ (by decide)]
    simp only [readSrc32, State.load32, he, ua.mem, ua.rd, ua.wr, hin, ite_true]
    simpa only [readSrc32, State.load32, hin, ite_true] using hr
  refine wp_cons (add32_upd (d := .rax) hb) fun b ub => ?_
  have hbwords := (h.rax ua).rax ub
  have val : (b.gpr .rax).setWidth 32 = (v[k]'hk) + x := by rw [ub.gpr, ua.gpr]; simp
  have ea : b.ea (at_ .rdi (4 * k)) = s.ea (at_ .rdi (4 * k)) := by
    rw [ea_at, ea_at, ub.other _ (by decide), ua.other _ (by decide)]
  have es : b.ea (at_ .rsi (slotOff k)) = bufAt p (slotOff k) := by rw [ea_at, hbwords.rsi]
  refine WP.block_cons_iff.mpr ⟨_, store32_exec (by rw [ea, ub.wr, ua.wr]; exact hw), ?_⟩
  change WP isa (.block [.store32 (at_ .rsi (slotOff k)) .rax])
    {b with mem := b.mem.writeW (b.ea (at_ .rdi (4 * k))) ((b.gpr .rax).setWidth 32)} _
  rw [ea, val]
  refine WP.block_cons_iff.mpr ⟨_, store32_exec (by change InRegions b.wr (b.ea (at_ .rsi (slotOff k))) 4; rw [es, ub.wr, ua.wr]; exact hs),
    WP.block_nil ?_⟩
  change Words p _ {b with mem := (b.mem.writeW _ _).writeW (b.ea (at_ .rsi (slotOff k))) ((b.gpr .rax).setWidth 32)} ∧ _
  rw [es, val]
  exact ⟨(hbwords.store hd).slot hk h12 _, by change (b.mem.writeW _ _).writeW (b.ea (at_ .rsi (slotOff k))) _ = _; rw [es, ub.mem, ua.mem], ub.rd.trans ua.rd,
    ub.wr.trans ua.wr, fun r hr => (ub.other r hr).trans (ua.other r hr)⟩

def finishMem (p d : Addr) (k : Nat) (x : Word) (m : Mem) : Mem :=
  let m := m.writeW (bufAt d (4 * k)) x
  if k < 12 then m else m.writeW (bufAt p (slotOff k)) x

theorem finishMem_out {p d : Addr} (hd : (bR d).Disjoint (slotR p)) {k : Nat}
    (hk : k < 16) (x : Word) (m : Mem) (j : Nat) (hj : j < 16) :
    (finishMem p d k x m).readW (bufAt d (4 * j)) 32 =
      if k = j then x else m.readW (bufAt d (4 * j)) 32 := by
  have e : (m.writeW (bufAt d (4 * k)) x).readW (bufAt d (4 * j)) 32 =
      if k = j then x else m.readW (bufAt d (4 * j)) 32 := by
    by_cases eq : k = j
    · subst j; rw [ite_eq_left rfl, Mem.readW_writeW_self32]
    · rw [ite_eq_right eq, readW_writeW_off _ _ _ (by omega) (by omega) (by omega) (by omega)]
  unfold finishMem
  split
  · exact e
  · rename_i h12
    rw [Mem.readW_writeW_sep (hd.sep (contains_off (by omega) (by omega))
      (contains_off (by simp only [slotOff]; omega) (by simp only [slotOff]; omega))) (by decide)]
    exact e

theorem finishMem_frame (p d : Addr) {k : Nat} (hk : k < 16) (x : Word) (m : Mem) :
    Frame [bR d, slotR p] m (finishMem p d k x m) := by
  have f : Frame [bR d, slotR p] m (m.writeW (bufAt d (4 * k)) x) :=
    (Frame.refl _ _).writeW (r := bR d) (by simp) _ (contains_off (by omega) (by omega))
  unfold finishMem
  split
  · exact f
  · rename_i hn
    exact f.writeW (r := slotR p) (by simp) _ (contains_off (by simp only [slotOff]; omega)
      (by simp only [slotOff]; omega))

theorem finish_word {p d : Addr} {v : Vector Word 16} {s : State} (h : Words p v s)
    (hdi : s.gpr .rdi = d) {k : Nat} (hk : k < 16) {x : Word}
    (hr : readSrc32 s (.mem (at_ .rdi (4 * k))) = some x)
    (hs : InRegions s.wr (bufAt p (slotOff k)) 4)
    (hw : InRegions s.wr (bufAt d (4 * k)) 4)
    (hd : (bR d).Disjoint (slotR p)) :
    WP isa (.block (fusedFinishWord k)) s fun t =>
      Words p (v.set k ((v[k]'hk) + x)) t ∧
      t.mem = finishMem p d k ((v[k]'hk) + x) s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rdi = d ∧ t.gpr .rsp = s.gpr .rsp := by
  have ea : s.ea (at_ .rdi (4 * k)) = bufAt d (4 * k) := by rw [ea_at, hdi]
  have sep : (slotR p).Disjoint ⟨s.ea (at_ .rdi (4 * k)), 4⟩ := by
    rw [ea]; exact hd.symm.sub_right (by simpa only [bufAt, ofInt_natCast] using
      (Offset.sub_base d (d := 4 * k) (n := 4) (k := 64) (by omega)))
  by_cases h12 : k < 12
  · exact WP.mono (finish_reg h h12 hr (ea ▸ hw) sep) fun t ⟨ht, mt, rd, wr, gr⟩ =>
      ⟨ht, by rw [finishMem, ite_eq_left h12, mt, ea], rd, wr,
        (gr _ (wreg_ne k h12).2.2.1.symm).trans hdi, gr _ (wreg_ne k h12).2.2.2.symm⟩
  · exact WP.mono (finish_slot h hk (by omega) hr hs (ea ▸ hw) sep) fun t ⟨ht, mt, rd, wr, gr⟩ =>
      ⟨ht, by rw [finishMem, ite_eq_right h12, mt, ea], rd, wr,
        (gr _ (by decide)).trans hdi, gr _ (by decide)⟩

def sumPrefix (v x : Vector Word 16) (n : Nat) : Vector Word 16 :=
  Vector.ofFn fun j => if j.1 < n then v[j] + x[j] else v[j]

theorem sumPrefix_set (v x : Vector Word 16) {n : Nat} (hn : n < 16) :
    (sumPrefix v x n).set n (v[n] + x[n]) = sumPrefix v x (n + 1) := by
  apply Vector.ext
  intro j hj
  simp only [sumPrefix, Vector.getElem_set, Vector.getElem_ofFn]
  by_cases e : n = j
  · subst j; simp
  · rw [ite_eq_right e]
    by_cases h : j < n
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

structure FinishInv (p d : Addr) (v x : Vector Word 16) (s₀ : State) (n : Nat) (s : State) : Prop where
  words : Words p (sumPrefix v x n) s
  out : ∀ j (hj : j < 16), s.mem.readW (bufAt d (4 * j)) 32 =
    if j < n then v[j] + x[j] else x[j]
  frame : Frame [bR d, slotR p] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rdi : s.gpr .rdi = d
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem finish_step {p d : Addr} {v x : Vector Word 16} {s₀ s : State} {n : Nat}
    (hn : n < 16) (h : FinishInv p d v x s₀ n s)
    (hs : scR p ∈ s₀.wr) (hb : bR d ∈ s₀.wr) (hd : (bR d).Disjoint (slotR p)) :
    WP isa (.block (fusedFinishWord n)) s (FinishInv p d v x s₀ (n + 1)) := by
  have hw : InRegions s.wr (bufAt d (4 * n)) 4 := by rw [h.wr]; exact out_b hb (by omega)
  have hr : readSrc32 s (.mem (at_ .rdi (4 * n))) = some x[n] := by
    have hi : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi (4 * n))) 4 := by
      rw [ea_at, h.rdi]; exact VG.Proof.Scrypt.Memory.InRegions.right hw
    rw [ea_at, h.rdi] at hi
    simp only [readSrc32, State.load32, ea_at, h.rdi, hi, ite_true, h.out n hn,
      ite_eq_right (Nat.lt_irrefl n)]
  have val : (sumPrefix v x n)[n] = v[n] := by simp [sumPrefix]
  refine WP.mono (finish_word h.words h.rdi hn hr
    (by rw [h.wr]; exact out_sc hs (by simp only [slotOff]; omega)) hw hd) fun t ⟨ht, mt, rd, wr, di, sp⟩ => ?_
  rw [val] at ht mt
  rw [sumPrefix_set v x hn] at ht
  refine ⟨ht, fun j hj => ?_, ?_, rd.trans h.rd, wr.trans h.wr, di, sp.trans h.rsp⟩
  · rw [mt, finishMem_out hd hn _ _ j hj, h.out j hj]
    by_cases e : n = j
    · subst j; simp
    · rw [ite_eq_right e]
      by_cases hjn : j < n
      · rw [ite_eq_left hjn, ite_eq_left (by omega)]
      · rw [ite_eq_right hjn, ite_eq_right (by omega)]
  · rw [mt]; exact h.frame.trans (finishMem_frame p d hn _ _)


theorem finish_ok {p d : Addr} {v x : Vector Word 16} {s : State} (h : Words p v s)
    (ho : ∀ j (hj : j < 16), s.mem.readW (bufAt d (4 * j)) 32 = x[j])
    (hs : scR p ∈ s.wr) (hb : bR d ∈ s.wr) (hd : (bR d).Disjoint (slotR p))
    (hdi : s.gpr .rdi = d) :
    WP isa (.block ((List.range 16).flatMap fusedFinishWord)) s fun t =>
      Words p (v.zipWith (· + ·) x) t ∧
      (∀ j (hj : j < 16), t.mem.readW (bufAt d (4 * j)) 32 = v[j] + x[j]) ∧
      Frame [bR d, slotR p] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .rdi = d ∧ t.gpr .rsp = s.gpr .rsp := by
  have hzero : sumPrefix v x 0 = v := by ext j hj; simp [sumPrefix]
  have hfull : sumPrefix v x 16 = v.zipWith (· + ·) x := by
    apply Vector.ext
    intro j hj
    simp only [sumPrefix, Vector.getElem_ofFn, Vector.getElem_zipWith, ite_eq_left hj]
    rfl
  have ini : FinishInv p d v x s 0 s :=
    ⟨by rw [hzero]; exact h, fun j hj => by simpa using ho j hj, Frame.refl _ _, rfl, rfl, hdi, rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (f := fusedFinishWord) (N := 16) (FinishInv p d v x s)
    (fun k t hk ht => finish_step hk ht hs hb hd) 16 (Nat.le_refl _) s ini) fun t ht => ?_
  exact ⟨by rw [← hfull]; exact ht.words, fun j hj => by simpa only [ite_eq_left hj] using ht.out j hj,
    ht.frame, ht.rd, ht.wr, ht.rdi, ht.rsp⟩


def xorPrefix (v x : Vector Word 16) (n : Nat) : Vector Word 16 :=
  Vector.ofFn fun j => if j.1 < n then v[j] ^^^ x[j] else v[j]

theorem xorPrefix_set (v x : Vector Word 16) {n : Nat} (hn : n < 16) :
    (xorPrefix v x n).set n (v[n] ^^^ x[n]) = xorPrefix v x (n + 1) := by
  apply Vector.ext
  intro j hj
  simp only [xorPrefix, Vector.getElem_set, Vector.getElem_ofFn]
  by_cases e : n = j
  · subst j; simp
  · rw [ite_eq_right e]
    by_cases h : j < n
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

structure XorRegsInv (p d src : Addr) (v x : Vector Word 16) (s₀ : State) (n : Nat) (s : State) : Prop where
  words : Words p (xorPrefix v x n) s
  out : ∀ j (hj : j < 16), j < n → s.mem.readW (bufAt d (4 * j)) 32 = v[j] ^^^ x[j]
  bound : n ≤ 16
  frame : Frame [bR d] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rdi : s.gpr .rdi = d
  rax : s.gpr .rax = src
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem xor_regs_step {p d src : Addr} {v x : Vector Word 16} {s₀ s : State} {n : Nat}
    (hn : n < 12) (h : XorRegsInv p d src v x s₀ n s)
    (hx : ∀ j (hj : j < 16), s₀.mem.readW (bufAt src (4 * j)) 32 = x[j])
    (hi : bR src ∈ s₀.rd ++ s₀.wr) (hb : bR d ∈ s₀.wr)
    (hd : (bR d).Disjoint (slotR p)) (hsrc : (bR src).Disjoint (bR d)) :
    WP isa (.block (fusedXorWord n)) s (XorRegsInv p d src v x s₀ (n + 1)) := by
  have ea : s.ea (at_ .rdi (4 * n)) = bufAt d (4 * n) := by rw [ea_at, h.rdi]
  have hw : InRegions s.wr (s.ea (at_ .rdi (4 * n))) 4 := by
    rw [ea, h.wr]; exact out_b hb (by omega)
  have hr : readSrc32 s (.mem (at_ .rax (4 * n))) = some x[n] := by
    have hin : InRegions (s.rd ++ s.wr) (bufAt src (4 * n)) 4 := by
      rw [h.rd, h.wr]; exact ⟨_, hi, (contains_off (by omega) (by omega))⟩
    have mem := h.frame.readW (r := bR src) (a := bufAt src (4 * n)) (w := 32) (contains_off (by omega) (by omega))
      (fun R hR => by simp only [List.mem_singleton] at hR; subst R; exact hsrc) (by decide : 32 / 8 < 2 ^ 64)
    simp only [readSrc32, State.load32, ea_at, h.rax, hin, ite_true]
    rw [mem, hx n (by omega)]
  have sep : (slotR p).Disjoint ⟨s.ea (at_ .rdi (4 * n)), 4⟩ := by
    rw [ea]; exact hd.symm.sub_right (by simpa only [bufAt, ofInt_natCast] using
      (Offset.sub_base d (d := 4 * n) (n := 4) (k := 64) (by omega)))
  refine WP.mono (xor_reg h.words hn hr hw sep) fun t ⟨ht, mt, rd, wr, gr⟩ => ?_
  have val : (xorPrefix v x n)[n] = v[n] := by simp [xorPrefix]
  rw [val] at ht mt
  rw [xorPrefix_set v x (by omega)] at ht
  rw [ea] at mt
  refine ⟨ht, fun j hj hjn => ?_, by omega, ?_, rd.trans h.rd, wr.trans h.wr,
    (gr _ (wreg_ne n hn).2.2.1.symm).trans h.rdi,
    (gr _ (wreg_ne n hn).1.symm).trans h.rax, (gr _ (wreg_ne n hn).2.2.2.symm).trans h.rsp⟩
  · rw [mt]
    by_cases e : n = j
    · subst j; exact Mem.readW_writeW_self32 _ _ _
    · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega) (by omega)]
      exact h.out j hj (by omega)
  · rw [mt]; exact h.frame.writeW (r := bR d) (by simp) _ (contains_off (by omega) (by omega))

theorem xor_slot {p d src : Addr} {s : State} {k : Nat} (h12 : 12 ≤ k)
    (hsi : s.gpr .rsi = p) (hdi : s.gpr .rdi = d) (ha : s.gpr .rax = src)
    {v x : Word} (hv : s.mem.readW (bufAt p (slotOff k)) 32 = v)
    (hx : s.mem.readW (bufAt src (4 * k)) 32 = x)
    (hs : InRegions s.wr (bufAt p (slotOff k)) 4)
    (hi : InRegions (s.rd ++ s.wr) (bufAt src (4 * k)) 4)
    (ho : InRegions s.wr (bufAt d (4 * k)) 4) :
    WP isa (.block (fusedXorWord k)) s fun t =>
      t.mem = (s.mem.writeW (bufAt d (4 * k)) (v ^^^ x)).writeW (bufAt p (slotOff k)) (v ^^^ x) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rcx = (v ^^^ x).setWidth 64 ∧
      (∀ r, r ≠ .rcx → t.gpr r = s.gpr r) := by
  rw [fusedXorWord, ite_eq_right (by omega)]
  have read : readSrc32 s (.mem (at_ .rsi (slotOff k))) = some v := by
    simp only [readSrc32, ea_at, hsi, State.load32,
      VG.Proof.Scrypt.Memory.InRegions.right hs, ite_true, hv]
  refine wp_cons (mov32_upd (d := .rcx) read) fun a ua => ?_
  have hr : readSrc32 a (.mem (at_ .rax (4 * k))) = some x := by
    simp only [readSrc32, State.load32, ea_at, ua.other _ (by decide : Reg.rax ≠ .rcx),
      ha, ua.rd, ua.wr, ua.mem, hi, ite_true, hx]
  refine wp_cons (xor32_upd (d := .rcx) hr) fun b ub => ?_
  have val : b.gpr .rcx = (v ^^^ x).setWidth 64 := by rw [ub.gpr, ua.gpr]; simp
  have val32 : (b.gpr .rcx).setWidth 32 = v ^^^ x := by rw [val]; simp
  have ea : b.ea (at_ .rdi (4 * k)) = bufAt d (4 * k) := by
    rw [ea_at, ub.other _ (by decide), ua.other _ (by decide), hdi]
  have es : b.ea (at_ .rsi (slotOff k)) = bufAt p (slotOff k) := by
    rw [ea_at, ub.other _ (by decide), ua.other _ (by decide), hsi]
  refine WP.block_cons_iff.mpr ⟨_, store32_exec (by rw [ea, ub.wr, ua.wr]; exact ho), ?_⟩
  change WP isa (.block [.store32 (at_ .rsi (slotOff k)) .rcx])
    {b with mem := b.mem.writeW (b.ea (at_ .rdi (4 * k))) ((b.gpr .rcx).setWidth 32)} _
  rw [ea, val32]
  refine WP.block_cons_iff.mpr ⟨_, store32_exec (by
    change InRegions b.wr (b.ea (at_ .rsi (slotOff k))) 4
    rw [es, ub.wr, ua.wr]; exact hs), WP.block_nil ?_⟩
  refine ⟨?_, ub.rd.trans ua.rd, ub.wr.trans ua.wr, val,
    fun r hr => (ub.other r hr).trans (ua.other r hr)⟩
  change (b.mem.writeW _ _).writeW (b.ea (at_ .rsi (slotOff k))) _ = _
  rw [es, val32, ub.mem, ua.mem]

def tempR (p : Addr) : Region := ⟨bufAt p 48, 8⟩

structure XorSlotsInv (p d src : Addr) (v x : Vector Word 16) (s₀ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ j (hj : j < 12), j ≠ 0 → s.gpr (wreg j) = ((v[j]'(by omega)) ^^^ (x[j]'(by omega))).setWidth 64
  slots : ∀ j (hj : j < 16), 12 ≤ j → s.mem.readW (bufAt p (slotOff j)) 32 =
    if j < 12 + n then v[j] ^^^ x[j] else v[j]
  out : ∀ j (hj : j < 16), j < 12 + n → s.mem.readW (bufAt d (4 * j)) 32 = v[j] ^^^ x[j]
  zero : s.mem.readW (bufAt p 48) 64 = ((v[0]) ^^^ (x[0])).setWidth 64
  frame : Frame [bR d, scR p] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rdi : s.gpr .rdi = d
  rsi : s.gpr .rsi = p
  rax : s.gpr .rax = src
  rsp : s.gpr .rsp = s₀.gpr .rsp
  tight : Frame [bR d, slotR p, tempR p] s₀.mem s.mem

theorem xor_slots_step {p d src : Addr} {v x : Vector Word 16} {s₀ s : State} {n : Nat}
    (hn : n < 4) (h : XorSlotsInv p d src v x s₀ n s)
    (hx : ∀ j (hj : j < 16), s₀.mem.readW (bufAt src (4 * j)) 32 = x[j])
    (hi : bR src ∈ s₀.rd ++ s₀.wr) (hb : bR d ∈ s₀.wr) (hs : scR p ∈ s₀.wr)
    (hd : (bR d).Disjoint (scR p)) (hsd : (bR src).Disjoint (bR d))
    (hss : (bR src).Disjoint (scR p)) :
    WP isa (.block (fusedXorWord (12 + n))) s (XorSlotsInv p d src v x s₀ (n + 1)) := by
  have hk : 12 + n < 16 := by omega
  have hv : s.mem.readW (bufAt p (slotOff (12 + n))) 32 = v[12 + n] := by
    rw [h.slots _ hk (by omega), ite_eq_right (by omega)]
  have xi : s.mem.readW (bufAt src (4 * (12 + n))) 32 = x[12 + n] := by
    rw [h.frame.readW (r := bR src) (contains_off (by omega) (by omega)) (fun R hR => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact hsd
      · exact hss) (by decide), hx _ hk]
  refine WP.mono (xor_slot (by omega) h.rsi h.rdi h.rax hv xi
    (by rw [h.wr]; exact out_sc hs (by simp only [slotOff]; omega))
    (by rw [h.rd, h.wr]; exact ⟨_, hi, contains_off (by omega) (by omega)⟩)
    (by rw [h.wr]; exact out_b hb (by omega))) fun t ⟨mt, rd, wr, _, gr⟩ => ?_
  have mm : t.mem = finishMem p d (12 + n) (v[12 + n] ^^^ x[12 + n]) s.mem := by
    rw [finishMem, ite_eq_right (by omega)]; exact mt
  have ds : (bR d).Disjoint (slotR p) := hd.sub_right (Region.sub_prefix (by decide))
  refine ⟨fun j hj hj0 => ?_, fun j hj hj12 => ?_, fun j hj hjn => ?_, ?_, ?_,
    rd.trans h.rd, wr.trans h.wr, (gr _ (by decide)).trans h.rdi,
    (gr _ (by decide)).trans h.rsi, (gr _ (by decide)).trans h.rax, (gr _ (by decide)).trans h.rsp, ?_⟩
  · rw [gr _ (fun e => hj0 (wreg_inj j hj 0 (by decide) e)), h.regs j hj hj0]
  · rw [mt]
    by_cases e : j = 12 + n
    · subst j; rw [Mem.readW_writeW_self32, ite_eq_left (by omega)]
    · rw [readW_writeW_off _ _ _ (by omega) (by simp only [slotOff]; omega)
        (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)]
      rw [Mem.readW_writeW_sep (ds.symm.sep
        (contains_off (by simp only [slotOff]; omega) (by simp only [slotOff]; omega))
        (contains_off (by omega) (by omega))) (by decide), h.slots j hj hj12]
      by_cases hjn : j < 12 + n
      · rw [ite_eq_left hjn, ite_eq_left (by omega)]
      · rw [ite_eq_right hjn, ite_eq_right (by omega)]
  · rw [mm, finishMem_out ds hk _ _ j hj]
    by_cases e : 12 + n = j
    · subst j; rw [ite_eq_left rfl]
    · rw [ite_eq_right e]; exact h.out j hj (by omega)
  · rw [mt]
    rw [Mem.readW_writeW_sep (off_sep p (by decide) (by simp only [slotOff]; omega)
      (by decide) (by decide) (by simp only [slotOff]; omega)) (by decide)]
    rw [Mem.readW_writeW_sep (hd.symm.sep (contains_off (by decide) (by decide))
      (contains_off (by omega) (by omega))) (by decide), h.zero]
  · rw [mm]
    exact h.frame.trans ((finishMem_frame p d hk _ _).sub fun R hR => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact ⟨bR d, by simp, fun _ h => h⟩
      · exact ⟨scR p, by simp, Region.sub_prefix (by decide)⟩)
  · rw [mm]
    exact h.tight.trans ((finishMem_frame p d hk _ _).sub fun R hR => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact ⟨bR d, by simp, fun _ h => h⟩
      · exact ⟨slotR p, by simp, fun _ h => h⟩)


theorem xor_ok {p d src : Addr} {v x : Vector Word 16} {s : State} (h : Words p v s)
    (hx : ∀ j (hj : j < 16), s.mem.readW (bufAt src (4 * j)) 32 = x[j])
    (hi : bR src ∈ s.rd ++ s.wr) (hb : bR d ∈ s.wr) (hs : scR p ∈ s.wr)
    (hd : (bR d).Disjoint (scR p)) (hsd : (bR src).Disjoint (bR d))
    (hss : (bR src).Disjoint (scR p)) (hdi : s.gpr .rdi = d) (ha : s.gpr .rax = src) :
    WP isa (.block fusedXor) s fun t =>
      Words p (v.zipWith (· ^^^ ·) x) t ∧
      (∀ j (hj : j < 16), t.mem.readW (bufAt d (4 * j)) 32 = v[j] ^^^ x[j]) ∧
      Frame [bR d, slotR p, tempR p] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .rdi = d ∧ t.gpr .rsp = s.gpr .rsp := by
  have hzero : xorPrefix v x 0 = v := by ext j hj; simp [xorPrefix]
  have ini : XorRegsInv p d src v x s 0 s :=
    ⟨by rw [hzero]; exact h, fun _ _ hj => by omega, by decide, Frame.refl _ _, rfl, rfl, hdi, ha, rfl⟩
  have hdslot : (bR d).Disjoint (slotR p) := hd.sub_right (Region.sub_prefix (by decide))
  unfold fusedXor
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (f := fusedXorWord) (N := 12)
    (XorRegsInv p d src v x s) (fun k t hk ht => xor_regs_step hk ht hx hi hb hdslot hsd)
    12 (Nat.le_refl _) s ini) fun a aa => ?_
  have zero : a.gpr .rcx = (v[0] ^^^ x[0]).setWidth 64 := by
    have := aa.words.regs 0 (by decide)
    simpa [wreg, xorPrefix] using this
  refine Proof.MdStream.X86_64.wp_store (a := bufAt p 48) (by rw [ea_at, aa.words.rsi])
    (by rw [aa.wr]; exact out_sc hs (by decide)) fun b gb mb rb wb => WP.block_nil ?_
  rw [zero] at mb
  have ib : XorSlotsInv p d src v x s 0 b := by
    refine ⟨fun j hj hj0 => ?_, fun j hj hj12 => ?_, fun j hj hjn => ?_, ?_, ?_,
      rb.trans aa.rd, wb.trans aa.wr, by rw [gb, aa.rdi], by rw [gb, aa.words.rsi],
      by rw [gb, aa.rax], by rw [gb, aa.rsp], ?_⟩
    · rw [gb, aa.words.regs j hj]
      simp only [xorPrefix, Vector.getElem_ofFn, ite_eq_left hj]
      rfl
    · rw [mb, readW_writeW_off _ _ _ (by decide) (by simp only [slotOff]; omega)
        (by decide) (by simp only [slotOff]; omega), aa.words.slots j hj hj12]
      simp only [xorPrefix, Vector.getElem_ofFn, Nat.add_zero]
      rfl
    · rw [mb, Mem.readW_writeW_sep (hd.sep (contains_off (by omega) (by omega))
        (contains_off (by decide) (by decide))) (by decide)]
      exact aa.out j hj (by omega)
    · rw [mb, Mem.readW_writeW_self64]
    · rw [mb]
      exact (aa.frame.sub (fun R hR => ⟨R, by simp only [List.mem_singleton] at hR; subst R; simp,
        fun _ h => h⟩)).writeW (r := scR p) (by simp) _ (contains_off (by decide) (by decide))
    · rw [mb]
      exact (aa.frame.sub (fun R hR => ⟨R, by simp only [List.mem_singleton] at hR; subst R; simp,
        fun _ h => h⟩)).writeW (r := tempR p) (by simp) _ (Region.contains_self _ _)
  refine WP.mono (wp_range_flatMap (M := isa) (f := fun k => fusedXorWord (12 + k)) (N := 4)
    (XorSlotsInv p d src v x s) (fun k t hk ht => xor_slots_step hk ht hx hi hb hs hd hsd hss)
    4 (Nat.le_refl _) b ib) fun c cc => ?_
  refine Proof.MdStream.X86_64.wp_movm (a := bufAt p 48) (by rw [ea_at, cc.rsi])
    (by rw [cc.rd, cc.wr]; exact VG.Proof.Scrypt.Memory.InRegions.right (out_sc hs (by decide)))
    fun t u => WP.block_nil ?_
  refine ⟨⟨fun j hj => ?_, fun j hj hj12 => ?_, (u.other _ (by decide)).trans cc.rsi⟩,
    fun j hj => ?_, u.mem ▸ cc.tight, u.rd.trans cc.rd, u.wr.trans cc.wr,
    (u.other _ (by decide)).trans cc.rdi, (u.other _ (by decide)).trans cc.rsp⟩
  · simp only [Vector.getElem_zipWith]
    by_cases e : j = 0
    · subst j; rw [show wreg 0 = Reg.rcx from rfl, u.gpr, cc.zero]
    · rw [u.other _ (fun e' => e (wreg_inj j hj 0 (by decide) e')), cc.regs j hj e]
  · rw [u.mem, cc.slots j hj hj12, ite_eq_left (by omega)]
    simp only [Vector.getElem_zipWith]
  · rw [u.mem]; exact cc.out j hj (by omega)

theorem core_ok {p d src : Addr} {v x : Vector Word 16} {s : State} (h : Words p v s)
    (hx : ∀ j (hj : j < 16), s.mem.readW (bufAt src (4 * j)) 32 = x[j])
    (hi : bR src ∈ s.rd ++ s.wr) (hb : bR d ∈ s.wr) (hs : scR p ∈ s.wr)
    (hd : (bR d).Disjoint (scR p)) (hsd : (bR src).Disjoint (bR d))
    (hss : (bR src).Disjoint (scR p)) (hdi : s.gpr .rdi = d) (ha : s.gpr .rax = src) :
    WP isa fusedCore s fun t =>
      Words p (Spec.Scrypt.core (v.zipWith (· ^^^ ·) x)) t ∧
      (∀ j (hj : j < 16), t.mem.readW (bufAt d (4 * j)) 32 =
        (Spec.Scrypt.core (v.zipWith (· ^^^ ·) x))[j]) ∧
      Frame [bR d, slotR p, tempR p] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .rdi = d ∧ t.gpr .rsp = s.gpr .rsp := by
  refine WP.seq (WP.mono (xor_ok h hx hi hb hs hd hsd hss hdi ha)
    fun a ⟨wa, oa, fa, ra, wra, da, spa⟩ => ?_)
  refine WP.seq (WP.mono (wa.rounds (by rw [wra]; exact hs) 4)
    fun b ⟨wb, fb, rb, wrb, db, spb⟩ => ?_)
  have sep : (bR d).Disjoint (slotR p) := hd.sub_right (Region.sub_prefix (by decide))
  have ob : ∀ j (hj : j < 16), b.mem.readW (bufAt d (4 * j)) 32 = (v.zipWith (· ^^^ ·) x)[j] := by
    intro j hj
    rw [fb.readW (r := bR d) (contains_off (by omega) (by omega)) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst R; exact sep) (by decide), oa j hj]
    simp only [Vector.getElem_zipWith]
  refine WP.mono (finish_ok wb ob (by rw [wrb, wra]; exact hs)
    (by rw [wrb, wra]; exact hb) sep (db.trans da)) fun t ⟨wt, ot, ft, rt, wrt, dt, spt⟩ => ?_
  refine ⟨wt, ?_, fa.trans ((fb.sub ?_).trans (ft.sub ?_)), rt.trans (rb.trans ra),
    wrt.trans (wrb.trans wra), dt, spt.trans (spb.trans spa)⟩
  · intro j hj
    rw [ot j hj]
    simp only [Spec.Scrypt.core, Vector.getElem_zipWith]
  · intro R hR
    simp only [List.mem_singleton] at hR; subst R
    exact ⟨slotR p, by simp, fun _ h => h⟩
  · intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact ⟨bR d, by simp, fun _ h => h⟩
    · exact ⟨slotR p, by simp, fun _ h => h⟩

theorem core_rel : RelCT isa
    (fun s t => s.gpr .rax = t.gpr .rax ∧ s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi)
    fusedCore (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rax, .rdi, .rsi])
    (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2) (by taint_decide)

end VG.Proof.Scrypt.X86_64.Retained
