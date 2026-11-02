module

-- separate module: constant time, whose taint checks evaluate the code (its meta imports); `Verified.lean` imports it with the core's proof
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Fn
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Fn
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# The Miller–Rabin round on RISC-V: constant time

As `Proof/Rsa/RISCV64/PrivCT.lean`: two runs with the same public data
(`dataOf`: the working space's address and length, `w`, which is the
contract's leak, and the stack pointer) are related by `Two`
(`Proof/Bignum/RISCV64/PreCT.lean`) at each step. The frame's `alloc` and
`free` leak nothing (`relCT_alloc`); the taint analysis checks the frame's
address, the saving of the registers and `setup` from the working space's
address and the frame's, and everything after `setup` from the registers it
fixes, which depend only on the public data (`Φ3`: array 0's base, `w` and
the arrays' size); what each run satisfies after each piece follows from
correctness (`two_post`, `front_ok`). Nothing branches on memory: the loops
count `w`, the 16 windows of a word and the 16 entries of the table.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot slot_sep Arrays)
open VG.Proof.Rsa.Mont (numAt wOf wordAt arrAt)
open VG.Proof.MillerRabin.Round (compact Layout Prepared Keeps roundContract)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-! ## The public data -/

/-- The public data: the working space's address and length, `w` (the
contract's leak) and the stack pointer. -/
abbrev Data := Addr × BitVec 64 × Nat × Addr

def dataOf (s : State) : Data := (s.gpr .a0, s.gpr .a1, wOf s.mem (s.gpr .a0), s.sp)

theorem pub_data {s₁ s₂ : State} (h : (roundContract RISCV64.abi compact frameBytes).pub s₁ s₂) :
    dataOf s₁ = dataOf s₂ := by
  have e : frameBytes = 95 + 1 := rfl
  rw [e] at h
  sig_pub [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, RISCV64.abi,
    RISCV64.argRegs] at h
  obtain ⟨hsp, hw, h0, h1⟩ := h
  unfold dataOf
  rw [List.singleton_inj.mp hw, h0, h1, hsp]

/-! ## The states of a run -/

/-- On entry. -/
def Φ0 (d : Data) (s : State) : Prop := (roundContract RISCV64.abi compact frameBytes).pre s ∧ dataOf s = d

/-- In the frame. -/
def Φ1 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ u = allocd frameBytes s

/-- The frame's address in `t2`. -/
def Φ2 (d : Data) (u : State) : Prop :=
  ∃ s, Φ0 d s ∧ u = (allocd frameBytes s).write .t2 ((allocd frameBytes s).sp + BitVec.ofNat 64 0)

/-- After `setup`: the registers the core's addresses and counts read. -/
def Φ3 (d : Data) (u : State) : Prop :=
  u.gpr .a7 = off d.1 (slot d.2.2.1 0) ∧ u.gpr .t0 = BitVec.ofNat 64 d.2.2.1 ∧
    u.gpr .s5 = BitVec.ofNat 64 (8 * (d.2.2.1 + 2))

theorem pins_Φ2 : Pins Φ2 [.a0, .t2] := by
  rintro d u₁ u₂ ⟨s₁, ⟨-, h₁⟩, rfl⟩ ⟨s₂, ⟨-, h₂⟩, rfl⟩ r hr
  have e := h₁.trans h₂.symm
  simp only [dataOf, Prod.mk.injEq] at e
  obtain ⟨e0, -, -, esp⟩ := e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide)]
    exact e0
  · rw [RegUpd.gpr_write_self, RegUpd.gpr_write_self]
    simp only [allocd, esp]

theorem pins_Φ3 : Pins Φ3 [.a7, .t0, .s5] := by
  rintro d s₁ s₂ ⟨a, b, c⟩ ⟨a', b', c'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a, a']
  · rw [b, b']
  · rw [c, c']

/-! ## The steps, by correctness -/

theorem addSp_ok {d : Data} {u : State} (h : Φ1 d u) : WP isa (.block [.addSp .t2 0]) u (Φ2 d) := by
  obtain ⟨s, φ, rfl⟩ := h
  exact WP.block_cons_iff.mpr ⟨_, exec_addSp (imm := 0) (by decide), WP.block_nil ⟨s, φ, rfl⟩⟩

/-- Saving the registers and `setup`, as in `fn_correct`. -/
theorem front_ok {d : Data} {u : State} (h : Φ2 d u) : WP isa (.block (save ++ setup)) u (Φ3 d) := by
  obtain ⟨s, ⟨hpre, rfl⟩, rfl⟩ := h
  have h := preR_of hpre
  have hL := h.lay
  dsimp only [Layout, compact] at hL
  obtain ⟨-, ⟨-, -, -, -⟩, h4, h128, hspace, -⟩ := hL
  have hp := h.prep
  dsimp only [Prepared, compact] at hp
  obtain ⟨-, -, hinv, -, -, -, -, -⟩ := hp
  have hkw := h.kw
  have hnw := h.nw
  simp only [dataOf]
  generalize hBd : s.gpr .a0 = B at hkw hnw hspace h4 h128 hinv
  generalize hZd : (s.gpr .a1).toNat * 8 = Z at hkw hnw
  generalize hwd : wOf s.mem B = w at hspace h4 h128 hinv
  have hZ64 : Z ≤ 2 ^ 64 := by omega_using [hnw]
  have hZ : slot w 28 ≤ Z := by
    rw [show max (11 + 16) (max (27 + 1) (max (9 + 1) (10 + 1))) = 28 from rfl] at hspace
    change slot w 28 ≤ 8 * (s.gpr .a1).toNat at hspace
    rw [← hZd]; omega_using [hspace]
  have sl : ∀ j < 28, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt hj) hZ
  generalize hs0 : (allocd frameBytes s).write .t2 ((allocd frameBytes s).sp + BitVec.ofNat 64 0) = s₀
  have g0 : ∀ r, r ≠ .t2 → s₀.gpr r = s.gpr r := fun r hr => by
    rw [← hs0, RegUpd.gpr_write_of_ne _ _ hr]; rfl
  have t20 : s₀.gpr .t2 = fb s := by
    rw [← hs0, RegUpd.gpr_write_self]; simp only [allocd, BitVec.add_zero]
  have m0 : s₀.mem = s.mem := by rw [← hs0]; rfl
  have w0 : s₀.wr = kR s :: [wsR s] := by rw [← hs0, ← h.hwr]; rfl
  have hsp : 96 ≤ s.sp.toNat := h.sp1
  have hal16 := h.sp16
  have fbN : (fb s).toNat = s.sp.toNat - 96 := by
    simp only [fb, frameBytes]
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith)]
    simp only [BitVec.toNat_ofNat]
  have fbal : (fb s).toNat % 8 = 0 := by rw [fbN]; omega_arith
  rw [save_eq]
  refine Spill.save_ok (b := .t2) (l := savedL) (by rw [t20]; exact fbal)
    (fun p hp => ⟨by have := savedL_fits.1 p hp; exact this.1, by have := savedL_fits.1 p hp; exact this.2⟩)
    (fun p hp => by
      rw [w0, t20]
      exact ⟨kR s, List.mem_cons_self .., Offset.contains_base _ (savedL_le p hp)
        (by have := savedL_le p hp; unfold frameBytes at this; omega_arith)⟩) ?_
  generalize hs1 : ({ s₀ with mem := Spill.saveMem s₀.mem (s₀.gpr .t2) s₀.gpr savedL } : State) = s₁
  have f1 : Frame [kR s] s.mem s₁.mem := by
    rw [← hs1, ← m0, t20]
    exact Spill.saveMem_frame_base savedL_le (by decide) _ _ _
  have o1 : Outside B Z (2 ^ 64) s.mem s₁.mem :=
    frame_outside f1 (by rw [← hBd, ← hZd]; exact hkw)
  have g1 : s₁.gpr = s₀.gpr := by rw [← hs1]
  have w1 : s₁.wr = s₀.wr := by rw [← hs1]
  have hs : Scr s₁ B Z := Scr.of_mem (by rw [w1, w0, ← hBd, ← hZd]; simp) hnw (by rw [← hBd]; exact h.al)
  have wd1 : ∀ {d}, d + 8 ≤ Z → Mont.word s₁.mem B d = Mont.word s.mem B d :=
    fun hd => o1.word (.inl hd) (by omega_using [hd, hZ64])
  have h0 := slot_lt (w := w) (show 0 < 28 by decide)
  have h0' : slot w 0 = 256 := by simp [slot, Impl.Bignum.hdrBytes]
  exact WP.mono (setup_ok (N := A s₁.mem B w 0) hs (by rw [g1, g0 _ (by decide), hBd])
    (by
      rw [wd1 (d := 8 * sW) (by simp only [sW]; omega_using [h0, h0', hZ]), ← hwd]
      simp only [wOf, wordAt, Proof.Rsa.Mont.wWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rfl)
    h4 h128 hZ (by
      rw [wd1 (d := slot w 0) (by omega_using [h0, sl 0 (by decide)]),
        wd1 (d := 8 * sMinv) (by simp only [sMinv]; omega_using [h0, h0', hZ])]
      exact hinv) rfl) fun _ ⟨⟨hm, _⟩, _⟩ => ⟨hm.a7, hm.t0, hm.s5⟩

/-! ## Constant time -/

/-- Allocating and freeing a frame leaks nothing (as `PrivCT.lean`'s). -/
theorem relCT_alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocd bytes s ∧ b = allocd bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocd bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

theorem body_rel : RelCT isa (Two Φ1)
    (.seq (.block [.addSp .t2 0]) (.seq (.block (save ++ setup))
      (.seq core (.block (([.li .a0 1, .logic .and .a0 .a0 .s6] : List Instr) ++ restore))))) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := Φ2) (two_taint [] (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil)
    (by taint_decide)) fun _ _ h => addSp_ok h) ?_
  refine RelCT.seq (two_post (Ψ := Φ3) (two_taint _ pins_Φ2 (by taint_decide)) fun _ _ h => front_ok h) ?_
  exact two_taint _ pins_Φ3 (by taint_decide)

theorem round_rel : RelCT isa (Two Φ0) Impl.MillerRabin.RISCV64.round fun _ _ => True :=
  relCT_alloc (body_rel.mono (fun a b ⟨s, t, ⟨d, φs, φt, hsp⟩, ea, eb⟩ =>
    ⟨d, ⟨s, φs, ea⟩, ⟨t, φt, eb⟩, by rw [ea, eb]; simp only [allocd, hsp]⟩) fun _ _ h => h)

theorem round_ct : ConstantTime isa (roundContract RISCV64.abi compact frameBytes).pre
    (roundContract RISCV64.abi compact frameBytes).pub Impl.MillerRabin.RISCV64.round :=
  RelCT.constantTime (round_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, (pub_data hp).symm⟩, congrArg (·.2.2.2) (pub_data hp)⟩) fun _ _ h => h)

end VG.Proof.MillerRabin.RISCV64
