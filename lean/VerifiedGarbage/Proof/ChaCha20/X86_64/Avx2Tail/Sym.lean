import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Sym

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes: straight-line code

The symbolic evaluation of `Avx512Tail/Sym.lean`, for `ymm` registers (eight
doublewords, `p` in lane `p / 4`), on the same regions (`Avx512Tail.regn`):
the state (at `rdi`), `buf` (at `r9`, of which the first 256 bytes are
written) and `4 D` bytes of data (at `rsi`).
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Spec.ChaCha20 (Word)
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init Sym.setReg sel2 sel2_eq sel2_lt add_ofNat' ofInt_ofNat
  xidx xidx_lt xidx_inj zreg_xidx)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (baseR bsize wsize regn wregs slot slot_ok wsize_le Ctx
  bsize_le regn_contains in_regn in_regn')
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)

/-- Doubleword `p % 4` of lane `p / 4` of `r`. -/
abbrev yw (s : State) (r : XReg) (p : Nat) : Word := dword (s.lane r (p / 4)) (p % 4)

def T.eval (D : Nat) (s₀ : State) : T → Word
  | .reg r p => yw s₀ (zreg r) p
  | .mem b i => s₀.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 32
  | .add a b => T.eval D s₀ a + T.eval D s₀ b
  | .xor a b => T.eval D s₀ a ^^^ T.eval D s₀ b

/-- Lane `j` of `vperm2i128 a, b, n`, without zeroing: lane `k % 2` of `a`
or of `b`, `k` the two bits of `n` for `j`. -/
def permT (A B : Nat → T) (n : BitVec 8) (p : Nat) : T :=
  let k := (n.extractLsb' (4 * (p / 4)) 2).toNat
  (if k < 2 then A else B) (4 * (k % 2) + p % 4)

def step (D : Nat) (σ : Sym) : Instr → Option Sym
  | .vop (.vbin op .l256 d a b) =>
    if op = .vpaddd then some (σ.setReg (xidx d) fun p => .add (σ.reg (xidx a) p) (σ.reg (xidx b) p))
    else if op = .vpxor then some (σ.setReg (xidx d) fun p => .xor (σ.reg (xidx a) p) (σ.reg (xidx b) p))
    else if op = .vpor ∧ a = b then some (σ.setReg (xidx d) (σ.reg (xidx a)))
    else none
  | .vop (.vperm2i128 d a b n) =>
    if n.getLsbD 3 = false ∧ n.getLsbD 7 = false then
      some (σ.setReg (xidx d) (permT (σ.reg (xidx a)) (σ.reg (xidx b)) n))
    else none
  | .vmovdquLoad .l256 d m => (slot m 8 (bsize D)).map fun (b, i) => σ.setReg (xidx d) fun p => σ.mem b (i + p)
  | .vbroadcasti128 d m =>
    (slot m 4 (bsize D)).map fun (b, i) => σ.setReg (xidx d) fun p => σ.mem b (i + p % 4)
  | .vmovdquStore .l256 m r => (slot m 8 (wsize D)).map fun (b, i) =>
    { σ with
      mem := fun b' i' => if b' = b ∧ i ≤ i' ∧ i' < i + 8 then σ.reg (xidx r) (i' - i) else σ.mem b' i'
      dirty := true }
  | _ => none

def run (D : Nat) (σ : Sym) : List Instr → Option Sym
  | [] => some σ
  | i :: is => (step D σ i).bind fun σ' => run D σ' is

/-! ## The machine agrees -/

/-- The terms `σ` hold in `s`. -/
structure SRel (D : Nat) (σ : Sym) (s₀ s : State) : Prop where
  reg : ∀ r p, p < 8 → yw s r p = T.eval D s₀ (σ.reg (xidx r) p)
  mem : ∀ b i, b < 3 → i < bsize D b →
    s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = T.eval D s₀ (σ.mem b i)
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (wregs D s₀) s₀.mem s.mem
  clean : σ.dirty = false → s.mem = s₀.mem

theorem SRel.init (D : Nat) (s₀ : State) : SRel D Sym.init s₀ s₀ :=
  ⟨fun r p _ => by simp only [Sym.init, T.eval, zreg_xidx], fun _ _ _ _ => rfl, rfl, rfl, rfl,
    Frame.refl _ _, fun _ => rfl⟩

theorem SRel.setReg {D : Nat} {σ : Sym} {s₀ s s' : State} (h : SRel D σ s₀ s) {d : XReg} {f : Nat → T}
    (hz : ∀ r p, p < 8 → yw s' r p = if r = d then T.eval D s₀ (f p) else yw s r p)
    (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) :
    SRel D (σ.setReg (xidx d) f) s₀ s' := by
  refine ⟨fun r p hp => ?_, fun b i hb hi => by rw [hm]; exact h.mem b i hb hi, hg.trans h.gpr,
    hr.trans h.rd, hw.trans h.wr, hm ▸ h.frame, fun hd => hm.trans (h.clean hd)⟩
  rw [hz r p hp]
  simp only [Sym.setReg, xidx_inj]
  split
  · rfl
  · exact h.reg r p hp

theorem mod4_lt' (p : Nat) : p % 4 < 4 := Nat.mod_lt _ (by decide)

theorem yw_lk (s : State) (r : XReg) {l k : Nat} (hk : k < 4) :
    yw s r (4 * l + k) = dword (s.lane r l) k := by
  simp only [yw]; rw [show (4 * l + k) / 4 = l by omega, show (4 * l + k) % 4 = k by omega]

theorem lane_setV256_lt (s : State) (d r : XReg) (f : Nat → BitVec 128) {l : Nat} (hl : l < 2) :
    (s.setV .l256 d (f 0) (f 1)).lane r l = if r = d then f l else s.lane r l := by
  rw [State.lane_setV256]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp

theorem dword_read256 (m : Mem) (a : Addr) {p : Nat} (hp : p < 8) :
    dword ((m.readW a 256).extractLsb' (128 * (p / 4)) 128) (p % 4) =
      m.readW (a + BitVec.ofNat 64 (4 * p)) 32 := by
  rw [dword, extract_extract _ _ _ _ _ (by omega), show 128 * (p / 4) + 32 * (p % 4) = 8 * (4 * p) by omega]
  exact readW_extract m a (w := 256) (k := 4 * p) (n := 4) (by omega)

theorem ymm_extract (s : State) (r : XReg) {k : Nat} (hk : k < 8) :
    (s.ymm r).extractLsb' (8 * (4 * k)) (8 * 4) = dword (s.lane r (k / 4)) (k % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  by_cases h : k < 4
  · simp only [show 8 * (4 * k) + j < 128 by omega, ite_true, show k / 4 = 0 by omega]
    exact congrArg _ (by omega)
  · simp only [show ¬ 8 * (4 * k) + j < 128 by omega, ite_false, show k / 4 = 1 by omega,
      show (1 : Nat) ≠ 0 by decide]
    exact congrArg _ (by omega)

theorem perm2Lanes_eq (a b : Nat → BitVec 128) (n : BitVec 8) {j : Nat} (h : n.getLsbD (4 * j + 3) = false) :
    perm2Lanes a b n j =
      (if (n.extractLsb' (4 * j) 2).toNat < 2 then a else b) ((n.extractLsb' (4 * j) 2).toNat % 2) := by
  simp only [perm2Lanes, h, Bool.false_eq_true, ite_false]
  by_cases hk : (n.extractLsb' (4 * j) 2).toNat < 2
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]

/-- One instruction. -/
theorem sstep_ok {D : Nat} {s₀ : State} (hc : Ctx D s₀) {σ σ' : Sym} {s : State} (h : SRel D σ s₀ s)
    {i : Instr} (e : step D σ i = some σ') : ∃ s', exec i s = some s' ∧ SRel D σ' s₀ s' := by
  have hD := hc.small
  unfold step at e
  split at e
  · rename_i op d a b
    split at e
    · rename_i hop; subst hop; cases e
      refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
      simp only [yw, lane_vbin256]
      split
      · simp only [VBinOp.sse, T.eval, dword_paddd _ _ (mod4_lt' p)]
        rw [← yw, ← yw, h.reg a p hp, h.reg b p hp]
      · rfl
    · split at e
      · rename_i hop; subst hop; cases e
        refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
        simp only [yw, lane_vbin256]
        split
        · simp only [VBinOp.sse, T.eval, dword_pxor]
          rw [← yw, ← yw, h.reg a p hp, h.reg b p hp]
        · rfl
      · split at e
        · rename_i hor
          obtain ⟨rfl, rfl⟩ := hor
          cases e
          refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
          simp only [yw, lane_vbin256]
          split
          · simp only [VBinOp.sse, dword_por, BitVec.or_self]
            rw [← yw]; exact h.reg a p hp
          · rfl
        · cases e
  · rename_i d a b n
    split at e
    · rename_i hn
      cases e
      refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
      simp only [yw, VOp.exec]
      rw [lane_setV256_lt _ _ _ (perm2Lanes (s.lane a) (s.lane b) n) (by omega)]
      split
      · have h3 : n.getLsbD (4 * (p / 4) + 3) = false := by
          rcases (by omega : p / 4 = 0 ∨ p / 4 = 1) with e | e <;> rw [e]
          · exact hn.1
          · exact hn.2
        rw [perm2Lanes_eq _ _ _ h3]
        simp only [permT]
        have hk : (n.extractLsb' (4 * (p / 4)) 2).toNat < 4 := by
          have := (n.extractLsb' (4 * (p / 4)) 2).isLt; simpa using this
        split
        · rw [← yw_lk s a (mod4_lt' p)]; exact h.reg a _ (by omega)
        · rw [← yw_lk s b (mod4_lt' p)]; exact h.reg b _ (by omega)
      · rfl
    · cases e
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := in_regn' hc hb h.wr hi (by decide)
    refine ⟨s.setV .l256 d ((s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 256).extractLsb' 0 128)
      ((s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 256).extractLsb' 128 128),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    simp only [yw]
    rw [lane_setV256_lt _ _ _ (fun l => (s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 256).extractLsb'
      (128 * l) 128) (by omega)]
    split
    · rw [dword_read256 _ _ hp, add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p) hb (by omega)
    · rfl
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := in_regn' hc hb h.wr hi (by decide)
    refine ⟨s.setV .l256 d (s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 128),
      by simp only [exec, ea, State.load128, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    simp only [yw]
    rw [lane_setV256_lt _ _ _ (fun _ => s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (by omega)]
    split
    · rw [dword_readW _ _ (mod4_lt' p), add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p % 4) hb (by have := mod4_lt' p; omega)
    · rfl
  · rename_i m r
    obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have hi' : i + 8 ≤ bsize D b := Nat.le_trans hi (wsize_le D b)
    have hb0 : b = 1 ∨ b = 2 := by
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | e | e
      · simp [wsize] at hi
      · exact .inl e
      · exact .inr e
    have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := in_regn hc hb h.wr hi' (by decide)
    refine ⟨s.setMem (s.mem.writeW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) (s.ymm r)),
      by simp only [exec, ea, State.store256_eq, hin, ite_true], ⟨fun r' p hp => ?_,
      fun b' i' hb' hi'' => ?_, by simp [h.gpr], by simp [h.rd], by simp [h.wr], ?_, fun hd => by cases hd⟩⟩
    · simp only [yw, State.setMem_lane]; exact h.reg r' p hp
    · simp only [State.setMem_mem]
      by_cases hx : b' = b ∧ i ≤ i' ∧ i' < i + 8
      · obtain ⟨rfl, h₁, h₂⟩ := hx
        simp only [and_self, h₁, h₂, ite_true]
        rw [show (regn D s₀ b').base + BitVec.ofNat 64 (4 * i') =
            (regn D s₀ b').base + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 (4 * (i' - i)) by
          rw [add_ofNat']; congr 2; omega]
        refine (readW_writeW_inside s.mem _ (s.ymm r) (k := 4 * (i' - i)) (n := 4) (by omega)
          (by decide)).trans ?_
        rw [ymm_extract _ _ (by omega)]
        exact h.reg r _ (by omega)
      · rw [ite_eq_right hx]
        by_cases e : b' = b
        · subst e
          have hx' : i' + 1 ≤ i ∨ i + 8 ≤ i' := by omega
          have := bsize_le hD b'
          exact (readW_writeW_off s.mem _ (s.ymm r) (d := 4 * i') (e := 4 * i) (n := 4)
            (by omega) (by omega) (by omega)).trans (h.mem b' i' hb' hi'')
        · have f := (Frame.refl [regn D s₀ b] s.mem).writeW (List.mem_singleton_self _) (s.ymm r)
            (regn_contains hD s₀ (n := 8) hi')
          rw [f.readW (r := regn D s₀ b') (regn_contains hD s₀ (n := 1) (by omega))
            (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.d b' b hb' hb e)
            (by decide)]
          exact h.mem b' i' hb' hi''
    · simp only [State.setMem_mem]
      refine h.frame.writeW (r := if b = 1 then ⟨s₀.gpr .r9, 256⟩ else ⟨s₀.gpr .rsi, 4 * D⟩)
        (by rcases hb0 with rfl | rfl <;> simp [wregs]) _ ?_
      rcases hb0 with rfl | rfl
      · simp only [regn, baseR, Region.Contains, ite_true]
        simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega
      · simp only [regn, baseR, Region.Contains, show (2 : Nat) ≠ 1 by decide, ite_false]
        simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega
  · cases e

/-- A block of instructions. -/
theorem srun_ok {D : Nat} {s₀ : State} (hc : Ctx D s₀) :
    ∀ (is : List Instr) {σ σ' : Sym} {s : State}, SRel D σ s₀ s → run D σ is = some σ' →
      WP isa (.block is) s (SRel D σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srun_ok hc is h₁ e₂⟩

end VG.Proof.ChaCha20.X86_64.Avx2Tail
