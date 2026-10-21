module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemETo
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemE
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGD
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# The prepared 256-bit loops on fewer blocks than a group

`decR`, `encR` and `encToR` take any number of blocks from 1 on: after the
setup, `cmp r9, 16` sends fewer than 16 blocks to `remD` or `remE` at once,
without the loop, from the state the loop would start from (`Stitch.Ready`,
`StitchTo.ReadyTo`), which is that of the blocks after no group (`DInv`,
`EInvR`, `EInvRTo` for `e = 0`); and 16 or more to the loops, as before
(`decTailR_ok`, `encTailR_ok`, `encTailRTo_ok`), for which `SPre.ofLe` gives
back the 16 blocks their proofs assume.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64

/-- A lower bound on the blocks that the data meets. -/
theorem SPre.ofLe {s₀ : State} {lo lo' : Nat} (hp : SPre s₀ lo) (h : lo' ≤ nb s₀) : SPre s₀ lo' :=
  { hp with nb16 := h }

theorem SPreTo.ofLe {M : CtxMode} {s₀ : State} {lo lo' : Nat} (hp : SPreTo M s₀ lo) (h : lo' ≤ nb s₀) :
    SPreTo M s₀ lo' :=
  { hp with nb16 := h }

end VG.Proof.Gcm.X86_64.Stitch

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPost DPost EPostTo DInv AInv Ready CtxMode FinOk nb pp cp dp sp op
  hk y₀ ctb)
open VG.Proof.Gcm.X86_64.StitchZTo (ctbT)
open VG.Proof.Gcm.X86_64.StitchTo (ReadyTo AInvTo)
open VG.Impl.Gcm.X86_64.Stitch (ordD ordE dbody body first storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchR (remD remE tailE)
open VG.Proof.Gcm.X86_64.StitchZH (add9_ok)
open VG.Spec.Gcm (Block ghashFrom)

/-- `cmp r9, 16`. -/
theorem cmp9_ok (s : State) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .r9).toNat < 16)) ∧ s'.gpr = s.gpr ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    e16, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `Ready` holds of a state with the same registers, memory and lanes. -/
theorem Ready.keep {s₀ : State} {P : Nat → Nat → Block} {s s' : State} (hR : Ready s₀ P s) (g : s'.gpr = s.gpr)
    (l : ∀ r k, s'.lane r k = s.lane r k) (m : s'.mem = s.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    Ready s₀ P s' :=
  ⟨hR.a.yframe (rs := []) ⟨g, m, rd, wr, fun x _ k _ => l x k⟩ (by simp) (by simp) (by simp), by rw [g]; exact hR.rdx,
    by rw [g]; exact hR.rax, fun r h1 h2 h3 => by rw [g]; exact hR.gpr r h1 h2 h3,
    fun k hk j hj => by rw [m]; exact hR.pw k hk j hj, fun k hk => by rw [l]; exact hR.m1 k hk, by rw [l]; exact hR.y,
    by rw [l]; exact hR.y1⟩

theorem ReadyTo.keep {s₀ : State} {P : Nat → Nat → Block} {s s' : State} (hR : ReadyTo s₀ P s) (g : s'.gpr = s.gpr)
    (l : ∀ r k, s'.lane r k = s.lane r k) (m : s'.mem = s.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    ReadyTo s₀ P s' :=
  ⟨hR.a.yframe (rs := []) ⟨g, m, rd, wr, fun x _ k _ => l x k⟩ (by simp) (by simp) (by simp), by rw [g]; exact hR.rdx,
    by rw [g]; exact hR.rax, fun r h1 h2 h3 h4 => by rw [g]; exact hR.gpr r h1 h2 h3 h4,
    fun k hk j hj => by rw [m]; exact hR.pw k hk j hj, fun k hk => by rw [l]; exact hR.m1 k hk, by rw [l]; exact hR.y,
    by rw [l]; exact hR.y1⟩

/-- `r9 + 16`, for the number of blocks in `r9`. -/
theorem r9_add16 {s₀ : State} : s₀.gpr .r9 + 16 = BitVec.ofNat 64 (16 + (nb s₀ - 16 * 0)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show (16 : BitVec 64).toNat = 16 from rfl, BitVec.toNat_ofNat]
  show ((nb s₀) + 16) % 2 ^ 64 = (16 + (nb s₀ - 16 * 0)) % 2 ^ 64
  rw [Nat.mul_zero, Nat.sub_zero, Nat.add_comm]

/-- The blocks before the first group: none decrypted or hashed. -/
theorem dinv0 {s₀ : State} {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s) : DInv s₀ P 0 s :=
  ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
    fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩

/-- Decryption of fewer blocks than a group: all of them by `remD`. -/
theorem decSmall_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {P : Nat → Nat → Block} (hr : RemLaw (hk s₀) P)
    (h1 : 1 ≤ nb s₀) (hlt : nb s₀ < 16) {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq (.block [.alu .add .r9 (.imm 16)]) remD) s (DPost s₀) :=
  remD_ok hp hr (dinv0 hR) (by omega) (by omega)

/-- Encryption of fewer blocks than a group: all of them by `remE`. -/
theorem encSmall_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {P : Nat → Nat → Block} (hr : RemLaw (hk s₀) P)
    (h1 : 1 ≤ nb s₀) (hlt : nb s₀ < 16) {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq (.block [.alu .add .r9 (.imm 16)]) (remE .rdx)) s (EPost s₀) := by
  refine WP.seq (WP.mono (add9_ok s) fun s₁ ⟨a9, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_)
  have l : ∀ x k, k < 2 → s₁.lane x k = s.lane x k := fun x k hk => by
    rw [← State.zlane_lt2 _ _ hk, ← State.zlane_lt2 _ _ hk, l₁]
  refine remE_ok hp hr (e := 0) ?_ (by omega) (by omega)
  exact
    { a := ⟨Nat.zero_le _, fun k hk => by rw [l _ _ hk]; exact hR.a.ctr k hk,
        fun k hk => by rw [l _ _ hk]; exact hR.a.msk k hk, fun k hk => by rw [l _ _ hk]; exact hR.a.inc k hk,
        by rw [g₁ _ (by decide)]; exact hR.a.rdi, by rw [g₁ _ (by decide)]; exact hR.a.rsi,
        by rw [g₁ _ (by decide)]; exact hR.a.r10, by rw [m₁]; exact hR.a.frame,
        fun k hk => by rw [m₁]; exact hR.a.blocks k hk, by rw [rd₁]; exact hR.a.rd, by rw [wr₁]; exact hR.a.wr⟩
      rdx := by rw [g₁ _ (by decide), hR.rdx]; simp
      r9 := by rw [a9, hR.gpr _ (by decide) (by decide) (by decide)]; exact r9_add16
      rax := by rw [g₁ _ (by decide)]; exact hR.rax
      gpr := fun r h1 h2 h3 h4 => by rw [g₁ r h3]; exact hR.gpr r h1 h2 h4
      pw := fun k hk j hj => by rw [m₁]; exact hR.pw k hk j hj
      m1 := fun k hk => by rw [l _ _ hk]; exact hR.m1 k hk
      y := by rw [l _ _ (by decide), hR.y]; simp [ghashFrom]
      y1 := by rw [l _ _ (by decide)]; exact hR.y1 }

/-- `add r9, 16` and `add r8, rdx`. -/
theorem addR9R8_ok (t : State) :
    WP isa (.block [.alu .add .r9 (.imm 16), .alu .add .r8 (.reg .rdx)]) t fun t' =>
      t'.gpr .r9 = t.gpr .r9 + 16 ∧ t'.gpr .r8 = t.gpr .r8 + t.gpr .rdx ∧
      (∀ q, q ≠ .r9 → q ≠ .r8 → t'.gpr q = t.gpr q) ∧
      (∀ x l, t'.lane x l = t.lane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, State.setReg, e16, reduceCtorEq, ↓reduceIte,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun q h1 h2 => by simp only [h1, h2, ↓reduceIte], fun _ _ => rfl, trivial, trivial,
    trivial⟩

/-- Out-of-place encryption of fewer blocks than a group: all of them by
`remE .r8`, `r8` pointed at the plaintext. -/
theorem encToSmall_ok {M : CtxMode} {s₀ : State} {lo : Nat} (hp : SPreTo M s₀ lo) {P : Nat → Nat → Block}
    (hr : RemLaw (hk s₀) P) (h1 : 1 ≤ nb s₀) (hlt : nb s₀ < 16) {s : State} (hR : ReadyTo s₀ P s) :
    WP isa (.seq (.block [.alu .add .r9 (.imm 16), .alu .add .r8 (.reg .rdx)]) (remE .r8)) s (EPostTo s₀) := by
  refine WP.seq (WP.mono (addR9R8_ok s) fun s₁ ⟨a9, a8, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_)
  refine remETo_ok hp hr (e := 0) ?_ (by omega) (by omega)
  exact
    { le := Nat.zero_le _
      ctr := fun k hk => by rw [l₁]; exact hR.a.ctr k hk
      msk := fun k hk => by rw [l₁]; exact hR.a.msk k hk
      inc := fun k hk => by rw [l₁]; exact hR.a.inc k hk
      rdi := by rw [g₁ _ (by decide) (by decide)]; exact hR.a.rdi
      rsi := by rw [g₁ _ (by decide) (by decide)]; exact hR.a.rsi
      frame := by rw [m₁]; exact hR.a.frame
      blocks := fun k hk => absurd hk (by omega)
      rd := by rw [rd₁]; exact hR.a.rd
      wr := by rw [wr₁]; exact hR.a.wr
      rdx := by rw [g₁ _ (by decide) (by decide), hR.rdx]; simp
      r8 := by rw [a8, hR.a.r8, hR.rdx, BitVec.sub_add_cancel]; simp
      r9 := by rw [a9, hR.gpr _ (by decide) (by decide) (by decide) (by decide)]; exact r9_add16
      rax := by rw [g₁ _ (by decide) (by decide)]; exact hR.rax
      gpr := fun r h1 h2 h3 h4 h5 => by rw [g₁ r h4 h3]; exact hR.gpr r h1 h2 h3 h5
      pw := fun k hk j hj => by rw [m₁]; exact hR.pw k hk j hj
      m1 := fun k hk => by rw [l₁]; exact hR.m1 k hk
      y := by rw [l₁, hR.y]; simp [ghashFrom]
      y1 := by rw [l₁]; exact hR.y1 }

/-- After the setup: `cmp r9, 16`, then fewer blocks than a group by
`small`, the others by `big`. -/
theorem zeroTail_ok {s₀ : State} {Rdy : State → Prop} {Q : State → Prop} {small big : Prog isa}
    (hkeep : ∀ s s', Rdy s → s'.gpr = s.gpr → (∀ r k, s'.lane r k = s.lane r k) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Rdy s')
    (h9 : ∀ s, Rdy s → s.gpr .r9 = s₀.gpr .r9)
    (hsmall : nb s₀ < 16 → ∀ s, Rdy s → WP isa small s Q) (hbig : 16 ≤ nb s₀ → ∀ s, Rdy s → WP isa big s Q)
    {s : State} (hR : Rdy s) :
    WP isa (.seq (.block [.alu .cmp .r9 (.imm 16)]) (.ite .b small big)) s Q := by
  refine WP.seq (WP.mono (cmp9_ok s) fun s' ⟨cf, g, l, m, rd, wr⟩ => ?_)
  have hR' := hkeep s s' hR g l m rd wr
  rw [h9 s hR] at cf
  refine WP.ite (decide (nb s₀ < 16)) (by simp only [eval, cf]) (fun h => ?_) (fun h => ?_)
  · exact hsmall (by simpa using h) s' hR'
  · exact hbig (by simp at h; omega) s' hR'

end VG.Proof.Gcm.X86_64.StitchR
