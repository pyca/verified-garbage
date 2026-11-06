module

public import VerifiedGarbage.Impl.Modes.X86_64.CfbFinal
public import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# CFB of a message's last piece on x86-64: straight-line steps

`movs_ok`: a run of register moves whose destinations are distinct and none
of their sources (`cfbFinal`'s `entry` and `reload`).
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (movR)

/-- `mov d, r` for each pair `(d, r)`. -/
def movs (l : List (Reg × Reg)) : List Instr := l.map fun p => .mov p.1 (.reg p.2)

/-- The moves `l`, whose destinations are distinct and none of their
sources: each destination gets its source's value, and nothing else
changes. -/
theorem movs_ok : ∀ (l : List (Reg × Reg)) (s : State), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ∉ l.map Prod.snd) →
    ∃ s', runBlock isa (movs l) s = some s' ∧ (∀ p ∈ l, s'.gpr p.1 = s.gpr p.2) ∧
      (∀ x, x ∉ l.map Prod.fst → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.zf = s.zf
  | [], s, _, _ => ⟨s, rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | (d, r) :: l, s, hn, hd => by
    have hn' : (l.map Prod.fst).Nodup := (List.nodup_cons.mp hn).2
    have hdl : d ∉ l.map Prod.fst := (List.nodup_cons.mp hn).1
    have hd' : ∀ p ∈ l, p.1 ∉ l.map Prod.snd := fun p hp h =>
      hd p (List.mem_cons_of_mem _ hp) (List.mem_cons_of_mem _ h)
    have hdr : d ∉ l.map Prod.snd := fun h => hd (d, r) List.mem_cons_self (List.mem_cons_of_mem _ h)
    let s₁ := s.setReg d (s.gpr r)
    obtain ⟨s', e', v', o', m', rd', wr', z'⟩ := movs_ok l s₁ hn' hd'
    have hs₁ : ∀ x, x ≠ d → s₁.gpr x = s.gpr x := fun x h => RegUpd.gpr_setReg_of_ne _ _ h
    refine ⟨s', ?_, fun p hp => ?_, fun x hx => ?_, m', rd', wr', z'⟩
    · show runBlock isa (.mov d (.reg r) :: movs l) s = some s'
      rw [runBlock_cons]
      simp only [exec, readSrc, Option.map_some, runStep_some]
      exact e'
    · rcases List.mem_cons.mp hp with rfl | hp
      · rw [o' _ hdl, RegUpd.gpr_setReg_self]
      · rw [v' p hp, hs₁ _ (fun h => hdr (h ▸ List.mem_map_of_mem hp))]
    · have h1 : x ≠ d := fun h => hx (h ▸ List.mem_cons_self)
      have h2 : x ∉ l.map Prod.fst := fun h => hx (List.mem_cons_of_mem _ h)
      rw [o' x h2, hs₁ x h1]

/-- `add d, r`. -/
theorem addRR_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [.alu .add d (.reg r)] s = some s' ∧ s'.gpr d = s.gpr d + s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_, fun r' hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `shr r, k`. -/
theorem shrImm_ok (s : State) (r : Reg) {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 63) :
    ∃ s', runBlock isa [.shift .shr r k] s = some s' ∧ s'.gpr r = s.gpr r >>> k ∧
      (∀ x, x ≠ r → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, h1, h2, and_self,
    ↓reduceIte]; rfl, ?_, fun x hx => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hx, RegUpd.gpr_setFlags]

/-- `shl r, k`. -/
theorem shlImm_ok (s : State) (r : Reg) {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 63) :
    ∃ s', runBlock isa [.shift .shl r k] s = some s' ∧ s'.gpr r = s.gpr r <<< k ∧
      (∀ x, x ≠ r → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, h1, h2, and_self,
    ↓reduceIte]; rfl, ?_, fun x hx => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hx, RegUpd.gpr_setFlags]

/-- The whole blocks' length, `(len >> lg) << lg`, as a number. -/
theorem shr_shl {len lg : Nat} (hl : len < 2 ^ 64) :
    (BitVec.ofNat 64 len >>> lg) <<< lg = BitVec.ofNat 64 (2 ^ lg * (len / 2 ^ lg)) := by
  apply BitVec.eq_of_toNat_eq
  have hle : 2 ^ lg * (len / 2 ^ lg) ≤ len := Nat.mul_div_le len _
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt hl]
  have h' : len / 2 ^ lg * 2 ^ lg ≤ len := Nat.div_mul_le_self len _
  rw [Nat.mod_eq_of_lt (by omega : 2 ^ lg * (len / 2 ^ lg) < 2 ^ 64), Nat.mul_comm,
    Nat.mod_eq_of_lt (by omega)]

/-- `n = len >> lg`, the number of whole blocks. -/
theorem shr_ofNat {len lg : Nat} (hl : len < 2 ^ 64) :
    BitVec.ofNat 64 len >>> lg = BitVec.ofNat 64 (len / 2 ^ lg) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hl)]

/-- `cfbFinal`'s `rest`, from the data's address `D` in `Rd` and the length
`len` in `Rl`: `D + 2^lg ⌊len / 2^lg⌋` in `Rd`, `len mod 2^lg` in `Rl`, and ZF
set if that is 0; `rax` is clobbered. -/
theorem rest_ok (s : State) {Rd Rl : Reg} {lg : Nat} (h1 : 1 ≤ lg) (h2 : lg ≤ 63) (hdl : Rd ≠ Rl)
    (hd : Rd ≠ .rax) (hl : Rl ≠ .rax) {D : Addr} {len : Nat} (hD : s.gpr Rd = D)
    (hL : s.gpr Rl = BitVec.ofNat 64 len) (hlen : len < 2 ^ 64) :
    ∃ s', runBlock isa [.mov .rax (.reg Rl), .shift .shr .rax lg, .shift .shl .rax lg, .alu .add Rd (.reg .rax),
        .alu .sub Rl (.reg .rax)] s = some s' ∧
      s'.gpr Rd = D + BitVec.ofNat 64 (2 ^ lg * (len / 2 ^ lg)) ∧ s'.gpr Rl = BitVec.ofNat 64 (len % 2 ^ lg) ∧
      s'.zf = some (decide (len % 2 ^ lg = 0)) ∧
      (∀ x, x ≠ .rax → x ≠ Rd → x ≠ Rl → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rax Rl
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := shrImm_ok s₁ .rax h1 h2
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := shlImm_ok s₂ .rax h1 h2
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := addRR_ok s₃ Rd .rax
  obtain ⟨s₅, e₅, v₅, z₅, o₅, m₅, rd₅, wr₅⟩ := subReg_ok s₄ Rl .rax
  have hw : s₃.gpr .rax = BitVec.ofNat 64 (2 ^ lg * (len / 2 ^ lg)) := by
    rw [v₃, v₂, v₁, hL, shr_shl hlen]
  have hle : 2 ^ lg * (len / 2 ^ lg) ≤ len := Nat.mul_div_le len _
  have hsub : BitVec.ofNat 64 len - BitVec.ofNat 64 (2 ^ lg * (len / 2 ^ lg)) = BitVec.ofNat 64 (len % 2 ^ lg) := by
    rw [Nat.mod_eq_sub_mul_div]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen,
      Nat.mod_eq_of_lt (by omega : 2 ^ lg * (len / 2 ^ lg) < 2 ^ 64), Nat.mod_eq_of_lt (by omega : len - _ < 2 ^ 64)]
    rw [show 2 ^ 64 - 2 ^ lg * (len / 2 ^ lg) + len = (len - 2 ^ lg * (len / 2 ^ lg)) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hRl₃ : s₃.gpr Rl = BitVec.ofNat 64 len := by rw [o₃ _ hl, o₂ _ hl, o₁ _ hl, hL]
  have hrax₄ : s₄.gpr .rax = BitVec.ofNat 64 (2 ^ lg * (len / 2 ^ lg)) := by rw [o₄ _ (Ne.symm hd), hw]
  have hm : len % 2 ^ lg < 2 ^ 64 := by
    have : 2 ^ lg ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) h2
    have := Nat.mod_lt len (Nat.two_pow_pos lg)
    omega
  refine ⟨s₅, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, by rw [m₅, m₄, m₃, m₂, m₁], by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · have h : [Instr.mov .rax (.reg Rl), .shift .shr .rax lg, .shift .shl .rax lg, .alu .add Rd (.reg .rax),
        .alu .sub Rl (.reg .rax)] = [movR .rax Rl] ++ [.shift .shr .rax lg] ++ [.shift .shl .rax lg] ++
        [.alu .add Rd (.reg .rax)] ++ [.alu .sub Rl (.reg .rax)] := rfl
    rw [h, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃,
      Option.bind_some, e₄, Option.bind_some, e₅]
  · rw [o₅ _ hdl, v₄, o₃ _ hd, o₂ _ hd, o₁ _ hd, hD, hw]
  · rw [v₅, o₄ _ (Ne.symm hdl), hRl₃, hrax₄, hsub]
  · rw [z₅, o₄ _ (Ne.symm hdl), hRl₃, hrax₄, hsub]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this
      exact this
    · intro h; rw [h]; rfl
  · rw [o₅ _ h3, o₄ _ h2, o₃ _ h1, o₂ _ h1, o₁ _ h1]

/-- `wipe words` from `u`, with the `words` quadwords at `rsp + 8` in the
region `R` and in the region `P` that `u` may write: zero, and nothing else
changed. -/
theorem wipe_zero (R P : Region) (u : State) (hP : P ∈ u.wr) : ∀ words, 8 + 8 * words ≤ 2 ^ 64 →
    (∀ k < words, R.Contains (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * k)) 8) →
    (∀ k < words, P.Contains (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * k)) 8) →
    ∃ s', runBlock isa (Impl.StackScratch.X86_64.wipe words) u = some s' ∧ Frame [R] u.mem s'.mem ∧
      (∀ k < words, s'.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * k)) 64 = 0) ∧
      (∀ x, x ≠ .r11 → s'.gpr x = u.gpr x) ∧ s'.gpr .r11 = 0 ∧ s'.rd = u.rd ∧ s'.wr = u.wr
  | 0, _, _, _ => ⟨u.setReg32 .r11 0, by
      simp only [Impl.StackScratch.X86_64.wipe, Impl.StackScratch.X86_64.wipeStores, List.range_zero,
        List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some],
      Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun x hx => by simp [State.setReg32, State.setReg, hx], by simp [State.setReg32, State.setReg], rfl, rfl⟩
  | w + 1, hw, hc, hcP => by
    obtain ⟨s₁, e₁, f₁, z₁, g₁, r₁, rd₁, wr₁⟩ :=
      wipe_zero R P u hP w (by omega) (fun k hk => hc k (by omega)) (fun k hk => hcP k (by omega))
    have hsp : s₁.gpr .rsp = u.gpr .rsp := g₁ _ (by decide)
    have hin : InRegions s₁.wr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * w)) 8 :=
      ⟨P, by rw [wr₁]; exact hP, hcP w (by omega)⟩
    refine ⟨{ s₁ with mem := s₁.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * w)) (s₁.gpr .r11) }, ?_,
      f₁.writeW (List.mem_singleton_self _) _ (hc w (by omega)), fun k hk => ?_, g₁, r₁, rd₁, wr₁⟩
    · have h : Impl.StackScratch.X86_64.wipe (w + 1) = Impl.StackScratch.X86_64.wipe w ++
          ([.store { base := .rsp, disp := ((8 + 8 * w : Nat) : Int) } .r11] : List Instr) := by
        simp only [Impl.StackScratch.X86_64.wipe, Impl.StackScratch.X86_64.wipeStores, List.range_succ,
          List.map_append, List.map_cons, List.map_nil, List.cons_append]
      rw [h, runBlock_app, e₁, Option.bind_some, runBlock_cons]
      simp only [exec, State.store64, State.ea, BitVec.ofInt_natCast, hsp, hin, ↓reduceIte, runStep_some,
        runBlock_nil]
    · show (s₁.mem.writeW _ (s₁.gpr .r11)).readW _ 64 = 0
      by_cases hkw : k = w
      · subst hkw; rw [Mem.readW_writeW_self64, r₁]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), z₁ k (by omega)]

/-- `x - a + b = x - (a - b)`, for `b ≤ a`. -/
theorem sub_add_ofNat (x : Addr) {a b : Nat} (h : b ≤ a) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a - b) := by
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], ← BitVec.sub_sub, BitVec.sub_add_cancel]

/-- A block that loads no MXCSR keeps it. -/
theorem runBlock_mxcsr : ∀ (is : List Instr) (s s' : State), (∀ i ∈ is, loadsMxcsr i = false) →
    runBlock isa is s = some s' → s'.mxcsr = s.mxcsr
  | [], s, s', _, h => by simp only [runBlock_nil, Option.some.injEq] at h; rw [h]
  | i :: is, s, s', hc, h => by
    rw [runBlock_cons] at h
    cases e : exec i s with
    | none => rw [e] at h; simp [runStep] at h
    | some s₁ =>
      rw [e, runStep_some] at h
      rw [runBlock_mxcsr is s₁ s' (fun j hj => hc j (List.mem_cons_of_mem _ hj)) h,
        exec_mxcsr (hc i List.mem_cons_self) e]

end VG.Proof.Modes.X86_64
