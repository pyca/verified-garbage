module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
meta import VerifiedGarbage.Impl.AesGcm.RISCV64
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-! ### `AesGcm.RISCV64.CTFin`, which this module and modules that import it used -/

section

/-! ### `AesGcm.RISCV64.CTCrypt`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: `crypt` is constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTCrypt.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the number of rounds (in `s3`), the data's
address and length, and the length of the text so far modulo 16; out of
place, also the source's address and the distance to the destination in
`s9` (`CT.taintWith`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

/-- Before `cryptWith o`. -/
def CrI (o : Bool) (c st w sp : Addr) (R : Nat) (S D : Addr) (n q : Nat) (s : State) : Prop :=
  ∃ V icb P, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ P % 16 = q ∧ CrIn o V sp R icb P S D n s

/-- Environments that agree on `s0` to `s3` agree in those registers. -/
theorem pinK {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State} (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂)
    (h28 : V₁ .s3 = V₂ .s3) (h29 : V₁ .s2 = V₂ .s2) (h30 : V₁ .s1 = V₂ .s1) (h31 : V₁ .s0 = V₂ .s0)
    {r : Reg} (hr : r ∈ [Reg.s3, .s2, .s1, .s0]) : s₁.gpr r = s₂.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.s3, e₂.s3, h28]
  · rw [e₁.s2, e₂.s2, h29]
  · rw [e₁.s1, e₂.s1, h30]
  · rw [e₁.s0, e₂.s0, h31]

/-- A piece checked by the taint analysis in place and, with `s9` public too,
out of place. -/
theorem CT.taintWith {I : State → Prop} (c : Bool → Prog isa) (o : Bool) (rs : List Reg)
    (hp : ∀ s₁ s₂, I s₁ → I s₂ → s₁.sp = s₂.sp ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      (o = true → s₁.gpr .s9 = s₂.gpr .s9))
    (hf : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs rs) (c false) h).isSome = true)
    (ht : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs (rs ++ ([.s9] : List Reg))) (c true) h).isSome = true) :
    CT I (c o) := by
  cases o
  · obtain ⟨_, hc⟩ := hf
    exact CT.taint rs (fun s₁ s₂ h₁ h₂ => ⟨(hp s₁ s₂ h₁ h₂).1, (hp s₁ s₂ h₁ h₂).2.1⟩) hc
  · obtain ⟨_, hc⟩ := ht
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ => ⟨(hp s₁ s₂ h₁ h₂).1, fun r hr => ?_⟩) hc
    rcases List.mem_append.mp hr with hr | hr
    · exact (hp s₁ s₂ h₁ h₂).2.1 r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact (hp s₁ s₂ h₁ h₂).2.2 rfl

/-- Out of place, `s9` is the distance in both runs. -/
theorem s9_eq {o : Bool} {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State} {S D : Addr}
    (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂) (d₁ : o = true → V₁ .s9 = D - S) (d₂ : o = true → V₂ .s9 = D - S) :
    o = true → s₁.gpr .s9 = s₂.gpr .s9 := fun ho => by
  rw [e₁.fr .s9 (by decide), e₂.fr .s9 (by decide), d₁ ho, d₂ ho]

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

/-! ### With the round keys bitsliced -/

/-- With the round keys bitsliced (`bs`): `s7` holds `b`, the buffer of the
round keys of the context for `R` rounds in `m₀`. -/
def BkB (bs : Bool) (b : Addr) (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (m₀ : Mem) (S D : Addr) (n : Nat)
    (s : State) : Prop :=
  bs = true → V .s7 = b ∧ BkIn (V .s7) (V .s2) (V .s1) (V .s0) sp R m₀ S D n s

/-- Before `cryptB bs o`. -/
def CrIB (bs o : Bool) (b c st w sp : Addr) (R : Nat) (S D : Addr) (n q : Nat) (s : State) : Prop :=
  ∃ V icb P, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ P % 16 = q ∧ CrIn o V sp R icb P S D n s ∧
    BkB bs b V sp R s.mem S D n s

/-- Part of the way: `j` bytes done. -/
def CrMB (bs o : Bool) (b c st w sp : Addr) (R : Nat) (S D : Addr) (n q j : Nat) (s : State) : Prop :=
  ∃ V icb P m₀, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ P % 16 = q ∧ CrMid o V sp R icb P S D n m₀ j s ∧
    BkB bs b V sp R m₀ S D n s

omit L in
/-- A piece checked by the taint analysis and, with the round keys bitsliced,
with `s7` public too. -/
theorem CT.taintBs {I : State → Prop} (c : Bool → Prog isa) (bs : Bool) (rs : List Reg)
    (hp : ∀ s₁ s₂, I s₁ → I s₂ → s₁.sp = s₂.sp ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      (bs = true → s₁.gpr .s7 = s₂.gpr .s7))
    (hf : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs rs) (c false) h).isSome = true)
    (ht : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs (rs ++ ([.s7] : List Reg))) (c true) h).isSome = true) :
    CT I (c bs) := by
  cases bs
  · obtain ⟨_, hc⟩ := hf
    exact CT.taint rs (fun s₁ s₂ h₁ h₂ => ⟨(hp s₁ s₂ h₁ h₂).1, (hp s₁ s₂ h₁ h₂).2.1⟩) hc
  · obtain ⟨_, hc⟩ := ht
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ => ⟨(hp s₁ s₂ h₁ h₂).1, fun r hr => ?_⟩) hc
    rcases List.mem_append.mp hr with hr | hr
    · exact (hp s₁ s₂ h₁ h₂).2.1 r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact (hp s₁ s₂ h₁ h₂).2.2 rfl

omit L in
/-- With the round keys bitsliced, `s7` is the buffer in both runs. -/
theorem s7_eq {bs : Bool} {b : Addr} {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State}
    (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂) (d₁ : bs = true → V₁ .s7 = b) (d₂ : bs = true → V₂ .s7 = b) :
    bs = true → s₁.gpr .s7 = s₂.gpr .s7 := fun hb => by
  rw [e₁.fr .s7 (by decide), e₂.fr .s7 (by decide), d₁ hb, d₂ hb]

omit L in
/-- `ctrArgsB bs 48`, from registers both runs agree on. -/
theorem ctrArgsB_ct {I : State → Prop} (bs : Bool)
    (hp : ∀ s₁ s₂, I s₁ → I s₂ → s₁.sp = s₂.sp ∧ (∀ r ∈ [Reg.s3, .s2, .s1, .s0], s₁.gpr r = s₂.gpr r) ∧
      (bs = true → s₁.gpr .s7 = s₂.gpr .s7)) : CT I (.block (ctrArgsB bs 48)) :=
  CT.taintBs (fun bs => .block (ctrArgsB bs 48)) bs _ hp ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩

theorem cryptWholeB_ct {bs o : Bool} {b : Addr} {R : Nat} {S D : Addr} {n q j : Nat} :
    CT (CrMB bs o b c st w sp R S D n q j) (cryptWholeB bs o) := by
  obtain ⟨nb, hnb⟩ : ∃ nb, nb = (n - j) / 16 := ⟨_, rfl⟩
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    V .s3 = BitVec.ofNat 64 R ∧ Env V sp s ∧ DataW (V .s2) (V .s1) (V .s0) s D n ∧
    DataOk (V .s1) (V .s0) s S n ∧ Alias o S D n ∧ j ≤ n ∧
    (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .a3 = D + BitVec.ofNat 64 j ∧
    (o = true → s.gpr .a6 = S + BitVec.ofNat 64 j) ∧ s.gpr .a4 = BitVec.ofNat 64 nb ∧
    BkB bs b V sp R s.mem S D n s
  refine CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs, hb⟩ => ?_) ?_
  · refine CT.taintWith (fun o => .block (splitCtrWith o)) o [.s4, .s5]
      (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, h₁, _⟩ ⟨_, _, _, _, _, _, _, _, h₂, _⟩ =>
        ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_, s9_eq h₁.env h₂.env h₁.dst h₂.dst⟩)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
  · refine WP.mono (splitCtrWith_ok hs.env hs.le hs.data.ok.lt (fun ho => by subst ho; exact hs.alias.eq) hs.dst
      hs.s4 hs.s5) fun s₁ ⟨h6, h6', h7, _, _, hg₁, hk₁⟩ => ?_
    exact ⟨V, h29, h30, h31, hs.s3, hs.env.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr hk₁.sp,
      hs.src.of_eq hk₁.rd hk₁.wr hk₁.sp, hs.alias, hs.le, hs.rounds, h6, h6', by rw [h7, hnb],
      fun hbs => ⟨(hb hbs).1, (((hb hbs).2.mid (L.v h29 h30 h31) hs).of_eq hk₁.rd hk₁.wr).memEq hk₁.mem⟩⟩
  · refine CT.ite (decide (nb = 0)) (fun s ⟨_, _, _, _, _, _, hd, _, _, _, _, _, _, h7, _⟩ =>
      eval_zero h7 (by have := hd.ok.lt; omega_arith)) (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
      Env V sp s ∧ DataW (V .s2) (V .s1) (V .s0) s D n ∧ DataOk (V .s1) (V .s0) s S n ∧ Alias o S D n ∧
      j ≤ n ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧
      s.gpr .a0 = V (keyReg bs) ∧ s.gpr .a1 = BitVec.ofNat 64 R ∧ s.gpr .a2 = V .s1 + BitVec.ofNat 64 48 ∧
      s.gpr .a3 = D + BitVec.ofNat 64 j ∧ s.gpr .a4 = BitVec.ofNat 64 nb ∧
      s.gpr .a5 = V .s0 + BitVec.ofNat 64 512 ∧ (o = true → s.gpr .a6 = S + BitVec.ofNat 64 j) ∧
      BkB bs b V sp R s.mem S D n s
    refine CT.seq (J := J₂) ?_
      (fun s ⟨V, h29, h30, h31, h28, he, hd, hsr, ha, hj, hR, h6, h6', h7, hb⟩ => ?_) ?_
    · exact ctrArgsB_ct bs fun s₁ s₂ ⟨_, a29, a30, a31, a28, e₁, _, _, _, _, _, _, _, _, k₁⟩
        ⟨_, b29, b30, b31, b28, e₂, _, _, _, _, _, _, _, _, k₂⟩ =>
        ⟨e₁.sp.trans e₂.sp.symm, fun r hr => pinK e₁ e₂ (a28.trans b28.symm) (a29.trans b29.symm)
          (a30.trans b30.symm) (a31.trans b31.symm) hr,
          s7_eq e₁ e₂ (fun h => (k₁ h).1) (fun h => (k₂ h).1)⟩
    · refine WP.mono (ctrArgsB_ok (bs := bs) he h28) fun s₂ ⟨a3, a4, a5, a8, hg₂, hk₂⟩ => ?_
      exact ⟨V, h29, h30, h31, he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr hk₂.sp,
        hsr.of_eq hk₂.rd hk₂.wr hk₂.sp, ha, hj, hR,
        a3, a4, a5, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6],
        by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h7], a8,
        fun ho => by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6' ho],
        fun hbs => ⟨(hb hbs).1, ((hb hbs).2.of_eq hk₂.rd hk₂.wr).memEq hk₂.mem⟩⟩
    · cases bs
      · cases o
        · refine CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, he₁, hd₁, _, _, hj₁, hR, a3, a4, a5, a6, a7, a8, _, _⟩
            ⟨V₂, b29, b30, b31, he₂, hd₂, _, _, _, _, b3, b4, b5, b6, b7, b8, _, _⟩ => ?_
          have hn₁ := hd₁.ok.lt
          have g₁ := ctrWhole_mk (L.v a29 a30 a31) he₁ a3 a4 a5 a6 a7 a8 hR (by omega_arith)
            (hd₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
          have g₂ := ctrWhole_mk (L.v b29 b30 b31) he₂ b3 b4 b5 b6 b7 b8 hR (by omega_arith)
            (hd₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
          rw [a29, a30, a31] at g₁
          rw [b29, b30, b31] at g₂
          exact ⟨_, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
        · refine ctrTo_rel fun s₁ s₂ ⟨⟨V₁, a29, a30, a31, he₁, hd₁, hs₁, ha₁, hj₁, hR, a3, a4, a5, a6, a7, a8, a9, _⟩,
            ⟨V₂, b29, b30, b31, he₂, hd₂, hs₂, ha₂, _, _, b3, b4, b5, b6, b7, b8, b9, _⟩⟩ => ?_
          have hn₁ := hd₁.ok.lt
          have g₁ := ctrWholeTo_mk (L.v a29 a30 a31) he₁ a3 a4 a5 a6 a7 a8 (a9 rfl) hR (by omega_arith)
            (hd₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
            (hs₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)) (ha₁.drop (by omega_arith))
          have g₂ := ctrWholeTo_mk (L.v b29 b30 b31) he₂ b3 b4 b5 b6 b7 b8 (b9 rfl) hR (by omega_arith)
            (hd₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
            (hs₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)) (ha₂.drop (by omega_arith))
          rw [a29, a30, a31] at g₁
          rw [b29, b30, b31] at g₂
          exact ⟨_, _, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
      · cases o
        · refine ctrBs_rel fun s₁ s₂ ⟨⟨V₁, a29, a30, a31, he₁, hd₁, _, _, hj₁, hR, a3, a4, a5, a6, a7, a8, _, k₁⟩,
            ⟨V₂, b29, b30, b31, he₂, hd₂, _, _, _, _, b3, b4, b5, b6, b7, b8, _, k₂⟩⟩ => ?_
          have hn₁ := hd₁.ok.lt
          obtain ⟨c₁, k₁⟩ := k₁ rfl
          obtain ⟨c₂, k₂⟩ := k₂ rfl
          have g₁ := ctrWholeBs_mk (L.v a29 a30 a31) he₁ a3 a4 a5 a6 a7 a8 hR (by omega_arith)
            (hd₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
            (k₁.sub (j := j) (k := 16 * nb) (by omega_arith))
          have g₂ := ctrWholeBs_mk (L.v b29 b30 b31) he₂ b3 b4 b5 b6 b7 b8 hR (by omega_arith)
            (hd₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
            (k₂.sub (j := j) (k := 16 * nb) (by omega_arith))
          rw [a29, a30, a31, c₁] at g₁
          rw [b29, b30, b31, c₂] at g₂
          exact ⟨_, _, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
        · refine ctrBsTo_rel fun s₁ s₂ ⟨⟨V₁, a29, a30, a31, he₁, hd₁, hs₁, ha₁, hj₁, hR, a3, a4, a5, a6, a7, a8, a9,
            k₁⟩, ⟨V₂, b29, b30, b31, he₂, hd₂, hs₂, ha₂, _, _, b3, b4, b5, b6, b7, b8, b9, k₂⟩⟩ => ?_
          have hn₁ := hd₁.ok.lt
          obtain ⟨c₁, k₁⟩ := k₁ rfl
          obtain ⟨c₂, k₂⟩ := k₂ rfl
          have g₁ := ctrWholeToBs_mk (L.v a29 a30 a31) he₁ a3 a4 a5 a6 a7 a8 (a9 rfl) hR (by omega_arith)
            (hd₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
            (hs₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)) (ha₁.drop (by omega_arith))
            (k₁.sub (j := j) (k := 16 * nb) (by omega_arith))
          have g₂ := ctrWholeToBs_mk (L.v b29 b30 b31) he₂ b3 b4 b5 b6 b7 b8 (b9 rfl) hR (by omega_arith)
            (hd₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
            (hs₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)) (ha₂.drop (by omega_arith))
            (k₂.sub (j := j) (k := 16 * nb) (by omega_arith))
          rw [a29, a30, a31, c₁] at g₁
          rw [b29, b30, b31, c₂] at g₂
          exact ⟨_, _, _, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩

theorem cryptTailB_ct {bs o : Bool} {b : Addr} {R : Nat} {S D : Addr} {n q j : Nat} :
    CT (CrMB bs o b c st w sp R S D n q j) (cryptTailB bs o) := by
  refine CT.ite (decide (n - j = 0)) (fun s ⟨_, _, _, _, _, _, _, _, hs, _⟩ =>
    eval_zero hs.s5 (by have := hs.data.ok.lt; omega_arith)) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    Env V sp s ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .a0 = V (keyReg bs) ∧ s.gpr .a1 = BitVec.ofNat 64 R ∧
    s.gpr .a2 = V .s1 + BitVec.ofNat 64 48 ∧ s.gpr .a3 = V .s1 + BitVec.ofNat 64 64 ∧
    s.gpr .a4 = BitVec.ofNat 64 1 ∧ s.gpr .a5 = V .s0 + BitVec.ofNat 64 512 ∧ BkB bs b V sp R s.mem S D n s
  let J₂ : State → Prop := fun s => ∃ V icb P m₀ s₀, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    TailKs o V sp R icb P S D n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs, hb⟩ => ?_) ?_)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs, hb⟩ =>
      WP.mono (tailKsB_ok (L.v h29 h30 h31) hs (hs.ciph (L.v h29 h30 h31)) fun hbs => (hb hbs).2) fun s' h =>
        ⟨V, icb, P, m₀, s, h29, h30, h31, h⟩) ?_
  · exact CT.taintBs (fun bs => .block (tailArgsB bs)) bs [.s3, .s2, .s1, .s0]
      (fun s₁ s₂ ⟨_, _, _, _, a29, a30, a31, _, h₁, k₁⟩ ⟨_, _, _, _, b29, b30, b31, _, h₂, k₂⟩ =>
        ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => pinK h₁.env h₂.env (h₁.s3.trans h₂.s3.symm)
          (a29.trans b29.symm) (a30.trans b30.symm) (a31.trans b31.symm) hr,
          s7_eq h₁.env h₂.env (fun h => (k₁ h).1) (fun h => (k₂ h).1)⟩)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
  · refine WP.mono (tailArgsB_ok (bs := bs) (L.v h29 h30 h31) hs.env hs.s3)
      fun s₂ ⟨hm₂, a3, a4, a5, a6, a7, a8, hg₂, hk₂⟩ => ?_
    exact ⟨V, h29, h30, h31, hs.env.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hs.rounds, a3, a4, a5, a6, a7, a8,
      fun hbs => ⟨(hb hbs).1, (hb hbs).2.tailArgs (L.v h29 h30 h31) hs hm₂ hk₂.rd hk₂.wr⟩⟩
  · cases bs
    · exact CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, he₁, hR, a3, a4, a5, a6, a7, a8, _⟩
        ⟨V₂, b29, b30, b31, he₂, _, b3, b4, b5, b6, b7, b8, _⟩ => by
        have g₁ := ctrTail_mk (L.v a29 a30 a31) he₁ a3 a4 a5 a6 a7 a8 hR
        have g₂ := ctrTail_mk (L.v b29 b30 b31) he₂ b3 b4 b5 b6 b7 b8 hR
        rw [a29, a30, a31] at g₁
        rw [b29, b30, b31] at g₂
        exact ⟨_, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
    · exact ctrBs_rel fun s₁ s₂ ⟨⟨V₁, a29, a30, a31, he₁, hR, a3, a4, a5, a6, a7, a8, k₁⟩,
        ⟨V₂, b29, b30, b31, he₂, _, b3, b4, b5, b6, b7, b8, k₂⟩⟩ => by
        obtain ⟨c₁, k₁⟩ := k₁ rfl
        obtain ⟨c₂, k₂⟩ := k₂ rfl
        have g₁ := ctrTailBs_mk (L.v a29 a30 a31) he₁ a3 a4 a5 a6 a7 a8 hR k₁
        have g₂ := ctrTailBs_mk (L.v b29 b30 b31) he₂ b3 b4 b5 b6 b7 b8 hR k₂
        rw [a29, a30, a31, c₁] at g₁
        rw [b29, b30, b31, c₂] at g₂
        exact ⟨_, _, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
  · refine CT.taintWith (fun o => .seq (.block ([.addi .a0 .s1 64, mov .a1 .s4] ++ toDst o .a4 ++ [mov .a2 .s5]))
      (xorLoopWith o)) o [.s4, .s5, .s1]
      (fun s₁ s₂ ⟨_, _, _, _, _, _, a30, _, h₁⟩ ⟨_, _, _, _, _, _, b30, _, h₂⟩ =>
        ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_, s9_eq h₁.env h₂.env h₁.mid.dst h₂.mid.dst⟩)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
    · rw [h₁.env.s1, h₂.env.s1, a30, b30]

theorem cryptB_ct {bs o : Bool} {b : Addr} {R : Nat} {S D : Addr} {n q : Nat} :
    CT (CrIB bs o b c st w sp R S D n q) (cryptB bs o) := by
  refine CT.ite (decide (n = 0)) (fun s ⟨_, _, _, _, _, _, _, hs, _⟩ => eval_zero hs.s5 hs.data.ok.lt)
    (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := CrMB bs o b c st w sp R S D n q j₁) ?_
    (fun s ⟨V, icb, P, h29, h30, h31, hP, hs, hb⟩ => WP.mono (WP.with_rdwr' (cryptFill_ok hs h0))
      fun s' ⟨⟨j, hj, hm⟩, rd, wr⟩ => ⟨V, icb, P, s.mem, h29, h30, h31, hP, by subst hj; rw [hP] at hm; exact hm,
        fun hbs => ⟨(hb hbs).1, (hb hbs).2.of_eq rd wr⟩⟩) ?_
  · refine CT.taintWith cryptFillWith o [.s4, .s5, .s6, .s1]
      (fun s₁ s₂ ⟨_, _, _, _, a30, _, hP₁, h₁, _⟩ ⟨_, _, _, _, b30, _, hP₂, h₂, _⟩ =>
        ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_, s9_eq h₁.env h₂.env h₁.dst h₂.dst⟩)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
    · rw [h₁.s6, h₂.s6, hP₁, hP₂]
    · rw [h₁.env.s1, h₂.env.s1, a30, b30]
  refine CT.seq (J := CrMB bs o b c st w sp R S D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWholeB_ct L)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs, hb⟩ =>
      WP.mono (WP.with_rdwr' (cryptWholeB_ok (L.v h29 h30 h31) hs (hs.ciph (L.v h29 h30 h31))
        fun hbs => (hb hbs).2)) fun s' ⟨⟨j, hj, hm, _⟩, rd, wr⟩ =>
        ⟨V, icb, P, m₀, h29, h30, h31, hP, by subst hj; exact hm,
          fun hbs => ⟨(hb hbs).1, (hb hbs).2.of_eq rd wr⟩⟩) (cryptTailB_ct L)

theorem crypt_ct {o : Bool} {R : Nat} {S D : Addr} {n q : Nat} :
    CT (CrI o c st w sp R S D n q) (cryptWith o) :=
  (cryptB_ct L (bs := false) (b := 0)).mono fun _ ⟨V, icb, P, h29, h30, h31, hP, hs⟩ =>
    ⟨V, icb, P, h29, h30, h31, hP, hs, Bool.noConfusion⟩

end

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: `tag`, `finTag` and `vg_aes_gcm_stream_finish` are constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTOpen.lean`): the invariants fix the context, the state,
`W`, the stack pointer, the number of rounds (`s3`), the lengths of the
additional data (`s10`) and of the text (`s11`), and the tag's address
(`s9`), all held in registers the environment pins.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- An environment with `R` rounds in `s3`. -/
def EnvR (c st w sp : Addr) (R : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ Env V sp s

/-- Before `finTag`: also `aad_len` (`A`) and `text_len` (`T`) in `s10` and `s11`. -/
def FTI (c st w sp : Addr) (R : Nat) (A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ V .s10 = A ∧
    V .s11 = T ∧ Env V sp s

/-- `EnvR`, and with the round keys bitsliced (`bs`), the buffer at `kb` in `s7`. -/
def EnvRB (bs : Bool) (kb c st w sp : Addr) (R : Nat) (S D : Addr) (n : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ Env V sp s ∧
    BkB bs kb V sp R s.mem S D n s

/-- `FTI`, and with the round keys bitsliced (`bs`), the buffer at `kb` in `s7`. -/
def FTIB (bs : Bool) (kb c st w sp : Addr) (R : Nat) (A T : BitVec 64) (S D : Addr) (n : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ V .s10 = A ∧
    V .s11 = T ∧ Env V sp s ∧ BkB bs kb V sp R s.mem S D n s

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem tagB_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {bs : Bool} {kb : Addr} {o R : Nat} (ho : o = 0 ∨ o = 112)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {S D : Addr} {n : Nat} :
    CT (EnvRB bs kb c st w sp R S D n) (tagB bs o) := by
  refine CT.seq (J := EnvRB bs kb c st w sp R S D n)
    ((lens_ct L (yo := 16) (.inr rfl)).mono fun s ⟨V, a, b, d, _, he, _⟩ => ⟨V, a, b, d, he⟩)
    (fun s ⟨V, a, b, d, e, he, hb⟩ => WP.mono (WP.with_rdwr' (lens_ok (L.v a b d) (.inr rfl) he rfl))
      fun s' ⟨h, rd, wr⟩ => ⟨V, a, b, d, e, h.1, fun hbs => ⟨(hb hbs).1,
        (hb hbs).2.frame hR h.2.2.2.2 (bk_tFrame (hb hbs).2) (ctx_tFrame (L.v a b d) he.stk') rd wr⟩⟩) ?_
  let J : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    Env V sp s ∧ s.gpr .a0 = V (keyReg bs) ∧ s.gpr .a1 = BitVec.ofNat 64 R ∧ s.gpr .a2 = V .s1 ∧
    s.gpr .a3 = V .s0 + BitVec.ofNat 64 o ∧ s.gpr .a4 = BitVec.ofNat 64 1 ∧
    s.gpr .a5 = V .s0 + BitVec.ofNat 64 512 ∧ BkB bs kb V sp R s.mem S D n s
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, he, hb⟩ => ?_) ?_
  · exact CT.taintBs (fun bs => .block (tagArgsB bs o)) bs [.s3, .s2, .s1, .s0]
      (fun s₁ s₂ ⟨_, a₁, b₁, d₁, e₁, h₁, k₁⟩ ⟨_, a₂, b₂, d₂, e₂, h₂, k₂⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => pinK h₁ h₂ (e₁.trans e₂.symm) (a₁.trans a₂.symm)
          (b₁.trans b₂.symm) (d₁.trans d₂.symm) hr, s7_eq h₁ h₂ (fun h => (k₁ h).1) (fun h => (k₂ h).1)⟩)
      (by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
      (by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
  · refine WP.mono (tagArgsB_ok (bs := bs) (L.v a b d) (o := o) ho he)
      fun s' ⟨hm, a3, a4, a5, a6, a7, a8, hg, hk⟩ => ⟨V, a, b, d, he.keep (fun r hr => hg r (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr, a3, by rw [a4, e], a5, a6, a7, a8,
        fun hbs => ⟨(hb hbs).1, (hb hbs).2.tagArgs (L.v a b d) ho hR hm hk.rd hk.wr⟩⟩
  · cases bs
    · exact CT.ctr fun s₁ s₂ ⟨V₁, a₁, b₁, d₁, e₁, a3, a4, a5, a6, a7, a8, _⟩
        ⟨V₂, a₂, b₂, d₂, e₂, b3, b4, b5, b6, b7, b8, _⟩ => by
        have g₁ := ctrTag_mk (L.v a₁ b₁ d₁) ho e₁ a3 a4 a5 a6 a7 a8 hR
        have g₂ := ctrTag_mk (L.v a₂ b₂ d₂) ho e₂ b3 b4 b5 b6 b7 b8 hR
        rw [a₁, b₁, d₁] at g₁
        rw [a₂, b₂, d₂] at g₂
        exact ⟨_, _, _, _, _, _, g₁, g₂, e₁.sp.trans e₂.sp.symm⟩
    · exact ctrBs_rel fun s₁ s₂ ⟨⟨V₁, a₁, b₁, d₁, e₁, a3, a4, a5, a6, a7, a8, k₁⟩,
        ⟨V₂, a₂, b₂, d₂, e₂, b3, b4, b5, b6, b7, b8, k₂⟩⟩ => by
        obtain ⟨c₁, k₁⟩ := k₁ rfl
        obtain ⟨c₂, k₂⟩ := k₂ rfl
        have g₁ := ctrTagBs_mk (L.v a₁ b₁ d₁) ho e₁ a3 a4 a5 a6 a7 a8 hR k₁
        have g₂ := ctrTagBs_mk (L.v a₂ b₂ d₂) ho e₂ b3 b4 b5 b6 b7 b8 hR k₂
        rw [a₁, b₁, d₁, c₁] at g₁
        rw [a₂, b₂, d₂, c₂] at g₂
        exact ⟨_, _, _, _, _, _, _, g₁, g₂, e₁.sp.trans e₂.sp.symm⟩

theorem tag_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (EnvR c st w sp R) (tag o) :=
  (tagB_ct L (bs := false) (kb := 0) (S := 0) (D := 0) (n := 0) ho hR).mono fun _ ⟨V, a, b, d, e, he⟩ =>
    ⟨V, a, b, d, e, he, Bool.noConfusion⟩

/-- The number of buffered bytes `finTag` pads: of the text if there is any,
else of the additional data. -/
abbrev finQ (A T : BitVec 64) : Nat := if T.toNat = 0 then A.toNat % 16 else T.toNat % 16

theorem finTagB_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {bs : Bool} {kb : Addr} {o R : Nat} (ho : o = 0 ∨ o = 112)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {A T : BitVec 64} {S D : Addr} {n : Nat} :
    CT (FTIB bs kb c st w sp R A T S D n) (finTagB bs o) := by
  have hq : finQ A T < 16 := by simp only [finQ]; split <;> exact Nat.mod_lt _ (by decide)
  let J : State → Prop := fun s => FTIB bs kb c st w sp R A T S D n s ∧ s.gpr .s6 = BitVec.ofNat 64 (finQ A T)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, f, g, he, hb⟩ => ?_) ?_
  · refine CT.ite (decide (T.toNat = 0)) (fun s ⟨_, _, _, _, _, _, g, he, _⟩ =>
      eval_zero (by rw [he.ofNat (r := .s11) (by decide), g]) T.isLt) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10])
          (.block [.logicImm .and .s6 .s10 15]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, f₁, _, h₁, _⟩ ⟨_, _, _, _, _, f₂, _, h₂, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s11])
          (.block [.logicImm .and .s6 .s11 15]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, g₁, h₁, _⟩ ⟨_, _, _, _, _, _, g₂, h₂, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h22 := he.fr .s10 (by decide)
    have h23 := he.fr .s11 (by decide)
    refine WP.ite (decide (T.toNat = 0)) (eval_zero (by rw [he.ofNat (r := .s11) (by decide), g]) T.isLt)
      (fun ht => ?_) (fun hf => ?_)
    · have hand := and15 (V .s10)
      have hQ : finQ A T = (V .s10).toNat % 16 := by simp only [finQ, f]; simp at ht; simp [ht]
      have h₃ : WP isa (.block [.logicImm .and .s6 .s10 15]) s fun s₃ =>
          s₃.gpr .s6 = BitVec.ofNat 64 ((V .s10).toNat % 16) ∧
            (∀ r, r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [Int.reduceNatCast', h22, hand]
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, e, f, g, he.keep (fun r hr => hg r
        (by revert r; decide)) hk.sp hk.rd hk.wr,
        fun hbs => ⟨(hb hbs).1, ((hb hbs).2.of_eq hk.rd hk.wr).memEq hk.mem⟩⟩, by rw [h26, hQ]⟩
    · have hand := and15 (V .s11)
      have hQ : finQ A T = (V .s11).toNat % 16 := by simp only [finQ, g]; simp at hf; simp [hf]
      have h₃ : WP isa (.block [.logicImm .and .s6 .s11 15]) s fun s₃ =>
          s₃.gpr .s6 = BitVec.ofNat 64 ((V .s11).toNat % 16) ∧
            (∀ r, r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [Int.reduceNatCast', h23, hand]
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, e, f, g, he.keep (fun r hr => hg r
        (by revert r; decide)) hk.sp hk.rd hk.wr,
        fun hbs => ⟨(hb hbs).1, ((hb hbs).2.of_eq hk.rd hk.wr).memEq hk.mem⟩⟩, by rw [h26, hQ]⟩
  refine CT.seq (J := FTIB bs kb c st w sp R A T S D n)
    ((flush_ct L (yo := 16) (.inr rfl) hq).mono fun s ⟨⟨V, a, b, d, _, _, _, he, _⟩, h26⟩ => ⟨⟨V, a, b, d, he⟩, h26⟩)
    (fun s ⟨⟨V, a, b, d, e, f, g, he, hb⟩, h26⟩ => WP.mono (WP.with_rdwr' (flush_ok (L.v a b d) (yo := 16) (.inr rfl)
      (x := List.replicate (finQ A T) 0) ⟨he, rfl⟩ (by simp [h26, Nat.mod_eq_of_lt hq]))) fun s' ⟨fl, rd, wr⟩ =>
        ⟨V, a, b, d, e, f, g, fl.env, fun hbs => ⟨(hb hbs).1,
          (hb hbs).2.frame hR fl.frame (bk_tFrame (hb hbs).2) (ctx_tFrame (L.v a b d) he.stk') rd wr⟩⟩) ?_
  refine CT.seq (J := EnvRB bs kb c st w sp R S D n) ?_ (fun s ⟨V, a, b, d, e, f, g, he, hb⟩ => ?_)
    ((tagB_ct L ho hR).mono fun _ h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10, .s11])
        (.block [mov .s4 .s10, mov .s6 .s11]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, f₁, g₁, h₁, _⟩ ⟨_, _, _, _, _, f₂, g₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h₅ : WP isa (.block [mov .s4 .s10, mov .s6 .s11]) s fun s₅ =>
        (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', mov]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => ⟨V, a, b, d, e, he.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr, fun hbs => ⟨(hb hbs).1, ((hb hbs).2.of_eq hk.rd hk.wr).memEq hk.mem⟩⟩

theorem finTag_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) {A T : BitVec 64} :
    CT (FTI c st w sp R A T) (finTag o) :=
  (finTagB_ct L (bs := false) (kb := 0) (S := 0) (D := 0) (n := 0) ho hR).mono
    fun _ ⟨V, a, b, d, e, f, g, he⟩ => ⟨V, a, b, d, e, f, g, he, Bool.noConfusion⟩

end

/-- In `finish`, after the entry: also the tag's address `Tp` in `s9`, which
the state may write. -/
def FinI (c st w sp : Addr) (R : Nat) (A T Tp : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s9 = Tp ∧ Env V sp s ∧ Covers [⟨Tp, 16⟩] s.wr

theorem finEntry_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6]) (.block finEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagOut_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s9, .s0]) (.block tagOut)
    h).isSome = true := ⟨_, by taint_decide⟩

theorem streamFinish_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa streamFinishRISCV64.pre streamFinishRISCV64.pub streamFinish := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, qsp⟩ := hq
  have h₁' : finPre σ₁ := h₁
  have L := finLay h₁'
  have hR := fin_R h₁'
  have dtw : (⟨σ₁.gpr .a5, 16⟩ : Region).Disjoint ⟨σ₁.gpr .a6, 16⟩ := by
    obtain ⟨-, -, -, -, -, -, -, dtw, -⟩ := h₁'
    exact dtw.sub_right (Region.sub_prefix (by decide))
  let I₀ : State → Prop := fun s => finPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, qsp.symm⟩, ?_⟩
  let FI := FinI (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a6) σ₁.sp (σ₁.gpr .a1).toNat (σ₁.gpr .a3) (σ₁.gpr .a4)
    (σ₁.gpr .a5)
  refine CT.seq (J := FI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := finEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  · refine WP.mono (fin1_wp (fin_W hs) (fin_al hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .a5, 16⟩] s₁.wr := by
      rw [h1.en.keeps.wr, hs.2.1]; exact covers_mem (by simp)
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.s2, e3]
    · rw [h1.s1, e5]
    · rw [h1.s0, e9]
    · rw [h1.s3, e4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [h1.s10, e6]
    · rw [h1.s11, e7]
    · rw [h1.s9, e8]
    · rw [← esp]; exact fin_env hs h1
    · rw [← e8]; exact hT
  refine CT.seq (J := FI)
    ((finTag_ct L (o := 0) (.inl rfl) hR).mono fun s ⟨V, a, b, d, e, f, g, _, he, _⟩ => ⟨V, a, b, d, e, f, g, he⟩)
    (fun s ⟨V, a, b, d, e, f, g, i, he, hT⟩ => WP.mono (WP.with_rdwr (finTag_ok (L.v a b d) (o := 0) (.inl rfl)
      (a := List.replicate ((σ₁.gpr .a3).toNat % 16) 0) (ct := List.replicate (σ₁.gpr .a4).toNat 0) he e hR rfl
      (by simp [f]) (by simp [g]))) fun s' ⟨fo, _, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, i, fo.env, by rw [wr]; exact hT⟩) ?_
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a6 ∧ s.sp = σ₁.sp) ?_
    (fun s ⟨V, a, b, d, e, f, g, i, he, hT⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT)
      (by rw [i, d]; exact dtw)) fun s' ⟨_, _, hg, hk⟩ =>
        ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, i₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a6) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64

end

end

/-! ### `AesGcm.RISCV64.CTOne`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: the pieces of `seal` and `open` are constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTOpen.lean`): the invariants fix the context, the state
at `W + 16`, `W`, the stack pointer, the rounds, the nonce, the additional
data and the data (their addresses and lengths, held in registers the
environment pins or, for the addresses of the additional data and the data,
in `W`), and leave the rest existential; their correctness lemmas carry them
from one piece to the next.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The registers and buffers of `seal` and `open` after the entry: the
context `c`, `W`, `R` rounds, the `n`-byte nonce (length in `s7`), the
additional data (`Ad` in `W + aadO`, length in `s10`) and the data (`D` in
`W + dataO`, length in `s11`), which the code reads; where it writes the
data (`D` itself, or out of place another buffer) is `OD`'s. -/
def OneI (c W sp : Addr) (R : Nat) (Np : Addr) (n : Nat) (Ad A D Ln : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = W + BitVec.ofNat 64 16 ∧ V .s0 = W ∧
    V .s3 = BitVec.ofNat 64 R ∧ V .s7 = BitVec.ofNat 64 n ∧ V .s10 = A ∧ V .s11 = Ln ∧ Env V sp s ∧
    DataOk (W + BitVec.ofNat 64 16) W s Np n ∧ DataOk (W + BitVec.ofNat 64 16) W s Ad A.toNat ∧
    DataOk (W + BitVec.ofNat 64 16) W s D Ln.toNat ∧ s.mem.readW (W + BitVec.ofNat 64 aadO) 64 = Ad ∧
    s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D

/-- Where `oneCryptWith o` writes the `Ln` bytes of data at `D`: to `Dst`
(`D` itself in place). -/
def OD (o : Bool) (c W : Addr) (D Dst Ln : BitVec 64) (s : State) : Prop :=
  DataW c (W + BitVec.ofNat 64 16) W s Dst Ln.toNat ∧ Alias o D Dst Ln.toNat

theorem OD.of_eq {o : Bool} {c W : Addr} {D Dst Ln : BitVec 64} {s s' : State} (h : OD o c W D Dst Ln s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : OD o c W D Dst Ln s' :=
  ⟨h.1.of_eq hrd hwr hsp, h.2⟩

section
variable {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln : BitVec 64}

/-- `OneI`, after code that keeps the frozen registers, the regions and the
slots of `W`. -/
theorem OneI.keep {s s' : State} (h : OneI c W sp R Np n Ad A D Ln s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (ha : s'.mem.readW (W + BitVec.ofNat 64 aadO) 64 = s.mem.readW (W + BitVec.ofNat 64 aadO) 64)
    (hd : s'.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s.mem.readW (W + BitVec.ofNat 64 dataO) 64) :
    OneI c W sp R Np n Ad A D Ln s' := by
  obtain ⟨V₀, a, b, d, e, f, i, k, he₀, hN, hA, hD, sa, sd⟩ := h
  have q : ∀ r ∈ frozen, V r = V₀ r := fun r hr => (hV r hr).trans (he₀.fr r hr)
  refine ⟨V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he, hN.of_eq hrd hwr hsp, hA.of_eq hrd hwr hsp, hD.of_eq hrd hwr hsp,
    ha.trans sa, hd.trans sd⟩
  · rw [q _ (by decide), a]
  · rw [q _ (by decide), b]
  · rw [q _ (by decide), d]
  · rw [q _ (by decide), e]
  · rw [q _ (by decide), f]
  · rw [q _ (by decide), i]
  · rw [q _ (by decide), k]

/-- `OneI`, after a block that keeps the frozen registers and the memory. -/
theorem OneI.block {s s' : State} (h : OneI c W sp R Np n Ad A D Ln s) (hg : ∀ r ∈ frozen, s'.gpr r = s.gpr r)
    (hk : Keeps s s') : OneI c W sp R Np n Ad A D Ln s' := by
  obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h
  exact ⟨V, a, b, d, e, f, i, k, he.keep hg hk.sp hk.rd hk.wr, hN.of_eq hk.rd hk.wr hk.sp,
    hA.of_eq hk.rd hk.wr hk.sp, hD.of_eq hk.rd hk.wr hk.sp, by rw [hk.mem]; exact sa, by rw [hk.mem]; exact sd⟩

variable (L : Lay c (W + BitVec.ofNat 64 16) W)
include L

omit L in
/-- `OneI` after a piece whose frame is apart from the slots. -/
theorem OneI.frame {s s' : State} (h : OneI c W sp R Np n Ad A D Ln s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneI c W sp R Np n Ad A D Ln s' :=
  h.keep hV he hrd hwr hsp (slot_keep hf (hs (by decide))) (slot_keep hf (hs (by decide)))

/-- Before `oneAad`: the nonce's address and length in `s4` and `s5`. -/
theorem oneAad_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : CT (fun s => OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n) oneAad := by
  -- `j0`
  refine CT.seq (J := fun s => OneI c W sp R Np n Ad A D Ln s ∧
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = 0)
    ((j0_ct L (Np := Np) (n := n)).mono fun s ⟨⟨V, a, b, d, _, f, _, _, he, hN, _⟩, h24, h25⟩ =>
      ⟨V, _, a, b, d, ⟨he, rfl, h24, h25, f, by rw [b, d]; exact hN⟩⟩)
    (fun s ⟨hs, h24, h25⟩ => by
      have hs' := hs
      obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
      exact WP.mono (WP.with_rdwr
        (j0_ok (L.v a b d) ⟨he, rfl, h24, h25, f, by rw [b, d]; exact hN⟩)) fun s' ⟨jo, rd, wr, sp'⟩ =>
        ⟨OneI.frame hs
          (fun r hr => (he.fr r hr).symm) jo.env rd wr sp' jo.frame (fun hd' => by
            rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'), by rw [← b]; exact jo.y⟩) ?_
  -- the additional data's arguments
  refine CT.seq (J := fun s => OneI c W sp R Np n Ad A D Ln s ∧
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = 0 ∧ s.gpr .s4 = Ad ∧
    s.gpr .s5 = BitVec.ofNat 64 A.toNat ∧ s.gpr .s6 = BitVec.ofNat 64 0) ?_
    (fun s ⟨hs, hy⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s0, .s10])
        (.block [.load .d .s4 .s0 aadO, mov .s5 .s10, .li .s6 0]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, i₁, _, h₁, _⟩, _⟩
      ⟨⟨_, _, _, d₂, _, _, i₂, _, h₂, _⟩, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.s0, h₂.s0, d₁, d₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    have h22 := he.ofNat (r := .s10) (by decide)
    have L' := L.v a b d
    have h₃ : WP isa (.block [.load .d .s4 .s0 aadO, mov .s5 .s10, .li .s6 0]) s fun s₃ =>
        s₃.gpr .s4 = Ad ∧ s₃.gpr .s5 = BitVec.ofNat 64 (V .s10).toNat ∧ s₃.gpr .s6 = BitVec.ofNat 64 0 ∧
          (∀ r, r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
      refine Steps.wp_ld (off := aadO) (a := V .s0 + BitVec.ofNat 64 aadO) (by decide) (by rw [he.s0])
        (L'.wal8 (by decide) (by decide)) (he.perm.wR (by decide)) fun s₃ u₃ => ?_
      refine Steps.wp_mv fun s₄ u₄ => Steps.wp_li (imm := 0) (by decide) fun s₅ u₅ => WP.block_nil ?_
      refine ⟨by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, d, sa], by
        rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), h22], u₅.gpr, fun r a b c => by
        rw [u₅.other _ c, u₄.other _ b, u₃.other _ a], ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [u₅.mem, u₄.mem, u₃.mem]
      · rw [u₅.rd, u₄.rd, u₃.rd]
      · rw [u₅.wr, u₄.wr, u₃.wr]
      · rw [u₅.sp, u₄.sp, u₃.sp]
    refine WP.mono h₃ fun s₃ ⟨a24, a25, a26, g₃, k₃⟩ =>
      ⟨OneI.block hs
        (fun r hr => g₃ r (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₃,
      by rw [k₃.mem]; exact hy, a24, by rw [a25, i], a26⟩
  -- the additional data absorbed
  refine CT.seq (J := fun s => OneI c W sp R Np n Ad A D Ln s) ?_
    (fun s ⟨hs, hy, h24, h25, h26⟩ => ?_) ?_
  · exact (absorb_ct L (yo := 16) (.inr rfl) (D := Ad) (n := A.toNat) (q := 0) (by decide)).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, he, _, hA, _⟩, _, h24, h25, h26⟩ =>
        ⟨V, blockAt s.mem (V .s2 + BitVec.ofNat 64 240), [], a, b, d, rfl,
          ⟨he, h24, h25, h26, by rw [b, d]; exact hA, rfl⟩⟩
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    exact WP.mono (WP.with_rdwr (absorb_ok (L.v a b d) (.inr rfl)
      (⟨he, h24, h25, h26, by rw [b, d]; exact hA, rfl⟩ : AbsIn V sp 16 _ [] Ad A.toNat s)))
      fun s' ⟨ab, rd, wr, sp'⟩ => OneI.frame hs (fun r hr => (he.fr r hr).symm) ab.env rd wr sp' ab.frame
        (fun hd' => by rw [← d]; exact slot_abs (L.v a b d) he.stk' hd')
  -- padded
  refine CT.seq (J := fun s => OneI c W sp R Np n Ad A D Ln s ∧
    s.gpr .s6 = BitVec.ofNat 64 (A.toNat % 16)) ?_ (fun s hs => ?_)
    ((flush_ct L (yo := 16) (.inr rfl) (q := A.toNat % 16) (Nat.mod_lt _ (by decide))).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, he, _⟩, h26⟩ => ⟨⟨V, a, b, d, he⟩, h26⟩)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10])
        (.block [.logicImm .and .s6 .s10 15]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, i₁, _, h₁, _⟩ ⟨_, _, _, _, _, _, i₂, _, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    have h22 := he.fr .s10 (by decide)
    have hand := and15 (V .s10)
    have h₅ : WP isa (.block [.logicImm .and .s6 .s10 15]) s fun s₅ =>
        s₅.gpr .s6 = BitVec.ofNat 64 ((V .s10).toNat % 16) ∧
          (∀ r, r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', h22, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨a26, g₅, k₅⟩ =>
      ⟨OneI.block hs
        (fun r hr => g₅ r (by revert r; decide)) k₅, by rw [a26, i]⟩

omit L in
/-- `OneI` without the nonce, which only `oneAad` reads, and with `K` in `s7`
(the nonce's length, or once `J₀` is done, the bitsliced round keys). -/
def OneIK (c W sp : Addr) (R : Nat) (K Ad A D Ln : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = W + BitVec.ofNat 64 16 ∧ V .s0 = W ∧
    V .s3 = BitVec.ofNat 64 R ∧ V .s7 = K ∧ V .s10 = A ∧ V .s11 = Ln ∧ Env V sp s ∧
    DataOk (W + BitVec.ofNat 64 16) W s Ad A.toNat ∧
    DataOk (W + BitVec.ofNat 64 16) W s D Ln.toNat ∧ s.mem.readW (W + BitVec.ofNat 64 aadO) 64 = Ad ∧
    s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D

omit L in
theorem OneI.toK {s : State} (h : OneI c W sp R Np n Ad A D Ln s) :
    OneIK c W sp R (BitVec.ofNat 64 n) Ad A D Ln s :=
  let ⟨V, a, b, d, e, f, i, k, he, _, hA, hD, sa, sd⟩ := h
  ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩

section
variable {K : BitVec 64}

omit L in
/-- `OneIK`, after code that keeps the frozen registers, the regions and the
slots of `W`. -/
theorem OneIK.keep {s s' : State} (h : OneIK c W sp R K Ad A D Ln s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (ha : s'.mem.readW (W + BitVec.ofNat 64 aadO) 64 = s.mem.readW (W + BitVec.ofNat 64 aadO) 64)
    (hd : s'.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s.mem.readW (W + BitVec.ofNat 64 dataO) 64) :
    OneIK c W sp R K Ad A D Ln s' := by
  obtain ⟨V₀, a, b, d, e, f, i, k, he₀, hA, hD, sa, sd⟩ := h
  have q : ∀ r ∈ frozen, V r = V₀ r := fun r hr => (hV r hr).trans (he₀.fr r hr)
  refine ⟨V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he, hA.of_eq hrd hwr hsp, hD.of_eq hrd hwr hsp,
    ha.trans sa, hd.trans sd⟩
  · rw [q _ (by decide), a]
  · rw [q _ (by decide), b]
  · rw [q _ (by decide), d]
  · rw [q _ (by decide), e]
  · rw [q _ (by decide), f]
  · rw [q _ (by decide), i]
  · rw [q _ (by decide), k]

omit L in
/-- `OneIK`, after a block that keeps the frozen registers and the memory. -/
theorem OneIK.block {s s' : State} (h : OneIK c W sp R K Ad A D Ln s) (hg : ∀ r ∈ frozen, s'.gpr r = s.gpr r)
    (hk : Keeps s s') : OneIK c W sp R K Ad A D Ln s' := by
  obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := h
  exact ⟨V, a, b, d, e, f, i, k, he.keep hg hk.sp hk.rd hk.wr,
    hA.of_eq hk.rd hk.wr hk.sp, hD.of_eq hk.rd hk.wr hk.sp, by rw [hk.mem]; exact sa, by rw [hk.mem]; exact sd⟩

omit L in
/-- `OneIK` after a piece whose frame is apart from the slots. -/
theorem OneIK.frame {s s' : State} (h : OneIK c W sp R K Ad A D Ln s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneIK c W sp R K Ad A D Ln s' :=
  h.keep hV he hrd hwr hsp (slot_keep hf (hs (by decide))) (slot_keep hf (hs (by decide)))

omit L in
theorem dataArgs_ct : CT (OneIK c W sp R K Ad A D Ln) (.block dataArgs) := by
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s11, .s0]) (.block dataArgs)
      h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, k₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, k₂, h₂, _⟩ =>
    ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · rw [h₁.s0, h₂.s0, d₁, d₂]

/-- `dataArgs`, for the invariants. -/
theorem dataArgs_one {s : State} (h : OneIK c W sp R K Ad A D Ln s) :
    WP isa (.block dataArgs) s fun s' => OneIK c W sp R K Ad A D Ln s' ∧ s'.gpr .s4 = D ∧
      s'.gpr .s5 = BitVec.ofNat 64 Ln.toNat ∧ s'.gpr .s6 = BitVec.ofNat 64 0 ∧ Keeps s s' := by
  have hs := h
  obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := h
  exact WP.mono (dataArgs_ok he (by rw [d]; exact L.wal) (by rw [d]; exact sd)) fun s' ⟨a24, a25, a26, g₁, k₁⟩ =>
    ⟨OneIK.block hs
      (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₁,
      a24, by rw [a25, k], a26, k₁⟩

/-- `oneCryptB bs o`: with the round keys bitsliced (`bs`), the buffer `kb`
in `s7`. -/
theorem oneCryptB_ct {bs o : Bool} {kb : Addr} {Dst : BitVec 64} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (fun s => OneIK c W sp R K Ad A D Ln s ∧ OD o c W D Dst Ln s ∧ (o = true → s.gpr .s9 = Dst - D) ∧
      (bs = true → K = kb ∧ BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D Dst Ln.toNat s))
      (oneCryptB bs o) := by
  refine CT.seq (J := fun s => (OneIK c W sp R K Ad A D Ln s ∧ s.gpr .s4 = D ∧
      s.gpr .s5 = BitVec.ofNat 64 Ln.toNat ∧ s.gpr .s6 = BitVec.ofNat 64 0) ∧ OD o c W D Dst Ln s ∧
      (o = true → s.gpr .s9 = Dst - D) ∧
      (bs = true → K = kb ∧ BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D Dst Ln.toNat s))
    (dataArgs_ct.mono fun s h => h.1)
    (fun s h => by
      have hs := h.1
      obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := h.1
      exact WP.mono (dataArgs_ok he (by rw [d]; exact L.wal) (by rw [d]; exact sd)) fun s' ⟨a24, a25, a26, g₁, k₁⟩ =>
        ⟨⟨OneIK.block hs (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₁,
          a24, by rw [a25, k], a26⟩,
          h.2.1.of_eq k₁.rd k₁.wr k₁.sp, fun ho => (g₁ _ (by decide) (by decide) (by decide)).trans (h.2.2.1 ho),
          fun hb => ⟨(h.2.2.2 hb).1, by rw [k₁.mem]; exact (h.2.2.2 hb).2.of_eq k₁.rd k₁.wr⟩⟩)
    ((cryptB_ct L (bs := bs) (b := kb) (o := o) (R := R) (S := D) (D := Dst) (n := Ln.toNat) (q := 0)).mono
      fun s ⟨⟨⟨V, a, b, d, e, f, _, k, he, _, hD, _⟩, h24, h25, h26⟩, ⟨hW, ha⟩, h9, hbk⟩ =>
        ⟨V, blockAt s.mem (V .s1 + BitVec.ofNat 64 48), 0, a, b, d, rfl,
          ⟨he, h24, h25, h26, e, hR, by rw [a, b, d]; exact hW, by rw [b, d]; exact hD, ha,
            fun ho => by rw [← he.fr .s9 (by decide)]; exact h9 ho⟩,
          fun hbs => ⟨f.trans (hbk hbs).1, by rw [f, a, b, d, (hbk hbs).1]; exact (hbk hbs).2⟩⟩)

/-- `oneTagB bs o`: with the round keys bitsliced (`bs`), the buffer `kb` in
`s7`. -/
theorem oneTagB_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {bs : Bool} {kb : Addr} {S' D' : Addr} {n' : Nat} {o : Nat}
    (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (fun s => OneIK c W sp R K Ad A D Ln s ∧
      (bs = true → K = kb ∧ BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem S' D' n' s)) (oneTagB bs o) := by
  let B : State → Prop := fun s => bs = true → K = kb ∧
    BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem S' D' n' s
  have hB : ∀ {s s' : State}, B s → Keeps s s' → B s' := fun hb hk hbs =>
    ⟨(hb hbs).1, by rw [hk.mem]; exact (hb hbs).2.of_eq hk.rd hk.wr⟩
  refine CT.seq (J := fun s => (OneIK c W sp R K Ad A D Ln s ∧ s.gpr .s4 = D ∧
      s.gpr .s5 = BitVec.ofNat 64 Ln.toNat ∧ s.gpr .s6 = BitVec.ofNat 64 0) ∧ B s)
    (dataArgs_ct.mono fun s h => h.1)
    (fun s h => WP.mono (dataArgs_one L h.1) fun s' ⟨h₁, a24, a25, a26, k₁⟩ => ⟨⟨h₁, a24, a25, a26⟩, hB h.2 k₁⟩) ?_
  refine CT.seq (J := fun s => OneIK c W sp R K Ad A D Ln s ∧ B s)
    ((absorb_ct L (yo := 16) (.inr rfl) (D := D) (n := Ln.toNat) (q := 0) (by decide)).mono
      fun s ⟨⟨⟨V, a, b, d, _, _, _, _, he, _, hD, _⟩, h24, h25, h26⟩, _⟩ =>
        ⟨V, blockAt s.mem (V .s2 + BitVec.ofNat 64 240), [], a, b, d, rfl,
          ⟨he, h24, h25, h26, by rw [b, d]; exact hD, rfl⟩⟩)
    (fun s ⟨⟨hs, h24, h25, h26⟩, hb⟩ => by
      have hs' := hs
      obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := hs'
      exact WP.mono (WP.with_rdwr (absorb_ok (L.v a b d) (.inr rfl)
        (⟨he, h24, h25, h26, by rw [b, d]; exact hD, rfl⟩ : AbsIn V sp 16 _ [] D Ln.toNat s)))
        fun s' ⟨ab, rd, wr, sp'⟩ => ⟨OneIK.frame hs (fun r hr => (he.fr r hr).symm) ab.env rd wr sp' ab.frame
          (fun hd' => by rw [← d]; exact slot_abs (L.v a b d) he.stk' hd'), fun hbs => ⟨(hb hbs).1,
          (hb hbs).2.frameJ0 L (by rw [← a, ← b, ← d]; exact he.stk') hR
            (rs := absFrame (W + BitVec.ofNat 64 16) W 16 sp)
            (by rw [← b, ← d]; exact ab.frame) abs16_j0 rd wr⟩⟩) ?_
  refine CT.seq (J := fun s => (OneIK c W sp R K Ad A D Ln s ∧ s.gpr .s6 = BitVec.ofNat 64 (Ln.toNat % 16)) ∧
    B s) ?_ (fun s ⟨hs, hb⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s11])
        (.block [.logicImm .and .s6 .s11 15]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, _, _, k₁, h₁, _⟩, _⟩ ⟨⟨_, _, _, _, _, _, _, k₂, h₂, _⟩, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := hs'
    have h23 := he.fr .s11 (by decide)
    have hand := and15 (V .s11)
    have h₅ : WP isa (.block [.logicImm .and .s6 .s11 15]) s fun s₅ =>
        s₅.gpr .s6 = BitVec.ofNat 64 ((V .s11).toNat % 16) ∧
          (∀ r, r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', h23, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨a26, g₅, k₅⟩ =>
      ⟨⟨OneIK.block hs (fun r hr => g₅ r (by revert r; decide)) k₅, by rw [a26, k]⟩, hB hb k₅⟩
  have hq : Ln.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  refine CT.seq (J := fun s => OneIK c W sp R K Ad A D Ln s ∧ B s)
    ((flush_ct L (yo := 16) (.inr rfl) hq).mono fun s ⟨⟨⟨V, a, b, d, _, _, _, _, he, _⟩, h26⟩, _⟩ =>
      ⟨⟨V, a, b, d, he⟩, h26⟩)
    (fun s ⟨⟨hs, h26⟩, hb⟩ => by
      have hs' := hs
      obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := hs'
      exact WP.mono (WP.with_rdwr (flush_ok (L.v a b d)
        (yo := 16) (.inr rfl) (x := List.replicate (Ln.toNat % 16) 0) ⟨he, rfl⟩ (by simp [h26])))
        fun s' ⟨fl, rd, wr, sp'⟩ => ⟨OneIK.frame hs (fun r hr => (he.fr r hr).symm) fl.env rd wr sp' fl.frame
          (fun hd' => by rw [← d]; exact slot_t (L.v a b d) he.stk' hd'), fun hbs => ⟨(hb hbs).1,
          (hb hbs).2.frameJ0 L (by rw [← a, ← b, ← d]; exact he.stk') hR
            (rs := tFrame (W + BitVec.ofNat 64 16) W 16 sp)
            (by rw [← b, ← d]; exact fl.frame) t16_j0 rd wr⟩⟩) ?_
  refine CT.seq (J := EnvRB bs kb c (W + BitVec.ofNat 64 16) W sp R S' D' n') ?_
    (fun s ⟨⟨V, a, b, d, e, f, i, k, he, _⟩, hb⟩ => ?_) ((tagB_ct L ho hR).mono fun _ h => h)
  · refine CT.taintBs (I := fun s => OneIK c W sp R K Ad A D Ln s ∧ B s)
      (fun _ => .block [mov .s4 .s10, mov .s6 .s11]) bs [.s10, .s11]
      (fun s₁ s₂ ⟨⟨_, _, _, _, _, f₁, i₁, k₁, h₁, _⟩, b₁⟩ ⟨⟨_, _, _, _, _, f₂, i₂, k₂, h₂, _⟩, b₂⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_, fun hbs => by
          rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]⟩)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · have h₅ : WP isa (.block [mov .s4 .s10, mov .s6 .s11]) s fun s₅ =>
        (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', mov]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => ⟨V, a, b, d, e, he.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr, fun hbs => ⟨f.trans (hb hbs).1, by
        rw [f, a, b, d, (hb hbs).1, hk.mem]; exact (hb hbs).2.of_eq hk.rd hk.wr⟩⟩

end

theorem oneCrypt_ct {o : Bool} {Dst : BitVec 64} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (fun s => OneI c W sp R Np n Ad A D Ln s ∧ OD o c W D Dst Ln s ∧ (o = true → s.gpr .s9 = Dst - D))
      (oneCryptWith o) :=
  (oneCryptB_ct L (bs := false) (kb := 0) hR).mono fun _ ⟨h, d, h9⟩ => ⟨h.toK, d, h9, Bool.noConfusion⟩

theorem oneTag_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (OneI c W sp R Np n Ad A D Ln) (oneTag o) :=
  (oneTagB_ct L (bs := false) (kb := 0) (S' := 0) (D' := 0) (n' := 0) ho hR).mono
    fun _ h => ⟨h.toK, Bool.noConfusion⟩

end

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. The entry loads `W` from the
stack argument at `sp + 8`, a public address, and then saves our caller's
registers through it: its head is checked on its own, and the rest from the
arguments and `W` (`oneHead_ct`). The pieces follow (`CTOne.lean`), with the
tag's address `T` in `s9`, which the environment pins, and, between them,
the additional data absorbed, for `oneTag 0`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The entry of `seal`, from its precondition. -/
theorem sealEntry_wp {s₀ : State} (h : sealPre s₀) :
    WP isa (.block (oneEntry 8)) s₀ fun s₁ =>
      OneI (s₀.gpr .a0) (stackArg s₀ 1) s₀.sp (s₀.gpr .a1).toNat (s₀.gpr .a2) (s₀.gpr .a3).toNat (s₀.gpr .a4)
        (s₀.gpr .a5) (s₀.gpr .a6) (s₀.gpr .a7) s₁ ∧
      s₁.gpr .s4 = s₀.gpr .a2 ∧ s₁.gpr .s5 = BitVec.ofNat 64 (s₀.gpr .a3).toNat ∧
      s₁.gpr .s9 = stackArg s₀ 0 ∧ Covers [⟨stackArg s₀ 0, 16⟩] s₁.wr ∧
      OD false (s₀.gpr .a0) (stackArg s₀ 1) (s₀.gpr .a6) (s₀.gpr .a6) (s₀.gpr .a7) s₁ := by
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, fW, fsp, hR, hstk,
    ca, wa⟩ := h
  have hk₀ : StkOk (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₀.sp :=
    one_stk hstk (by simp) (by simp)
  have hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 2] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hTd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 1)) :=
    ((dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).sub_right
      (Region.sub_prefix (show 8 ≤ 8 * 2 by decide))).symm
  refine WP.mono (one1_wp (off := 8) (W := stackArg s₀ 1) (T := stackArg s₀ 0) (.inl rfl) hW wa hstk.1
    (args_in hA (by decide) (i := 1) (by decide)) rfl (args_in hA (by decide) (i := 0) (by decide)) rfl hTd)
    fun s₁ h1 => ?_
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] s₁.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  have hDok : DataOk (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₁ (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
    ⟨covers_left hDw, (s₀.gpr .a7).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  refine ⟨⟨s₁.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3]; exact toN, by rw [h1.s7]; exact toN,
    h1.s10, h1.s11, one_env h1 hC hW hk₀, ?_, ?_, hDok, h1.aad, h1.dat⟩, h1.s4, by rw [h1.s5]; exact toN, h1.s9, ?_,
    ⟨⟨hDok, hDw, dcd⟩, rfl⟩⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a3).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a5).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · rw [hk₁.wr, hwr]; exact covers_mem (by simp)

/-- The head of the entry: `W`, the stack argument at `sp + off`, into `t1`. -/
theorem oneA_ok {s₀ : State} {off : Nat} {W : Addr} (hoff : off = 8 ∨ off = 16) (hsa : s₀.sp.toNat % 16 = 0)
    (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 off) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 off) 64 = W) :
    WP isa (.block [.addSp .t1 0, .load .d .t1 .t1 off]) s₀ fun sA =>
      sA.gpr .t1 = W ∧ (∀ r, r ≠ .t1 → sA.gpr r = s₀.gpr r) ∧ Keeps s₀ sA := by
  refine Steps.wp_addSp (imm := 0) (by decide) fun sA uA => ?_
  refine Steps.wp_ld (off := off) (a := s₀.sp + BitVec.ofNat 64 off) (by omega_using [hoff]) (by rw [uA.gpr, add_ofNat_zero])
    (Spill.al8 (by omega_using [hsa]) (by omega_using [hoff])) (by rw [uA.rd, uA.wr]; exact hWi) fun sB uB => WP.block_nil ?_
  exact ⟨by rw [uB.gpr, uA.mem, hWv], fun r hr => by rw [uB.other r hr, uA.other r hr],
    ⟨by rw [uB.mem, uA.mem], by rw [uB.rd, uA.rd], by rw [uB.wr, uA.wr], by rw [uB.sp, uA.sp]⟩⟩

/-- The rest of the entry, after `W` is in `t1`. -/
abbrev oneRestAt (tagO : Nat) : List Instr :=
  save .t1 ++ ([mov .s2 .a0, mov .s3 .a1, .addi .s1 .s0 16, mov .s4 .a2, mov .s5 .a3, mov .s7 .a3,
    .store .d .a4 .s0 aadO, mov .s10 .a5, .store .d .a6 .s0 dataO, mov .s11 .a7, .addSp .t1 0,
    .load .d .s9 .t1 tagO] : List Instr)

abbrev oneRest : List Instr := oneRestAt 0

theorem oneEntryAt_eq (off tagO : Nat) :
    oneEntryAt off tagO = ([.addSp .t1 0, .load .d .t1 .t1 off] : List Instr) ++ oneRestAt tagO := by
  rw [oneEntryAt, List.append_assoc]

theorem oneEntry_eq (off : Nat) : oneEntry off = ([.addSp .t1 0, .load .d .t1 .t1 off] : List Instr) ++ oneRest :=
  oneEntryAt_eq off 0

theorem oneHead_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 8]) h).isSome = true := ⟨_, by taint_decide⟩

/-- The head of `seal_bitsliced`'s entry, which loads `W` from `sp + 16`. -/
theorem oneHead16_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 16]) h).isSome = true := ⟨_, by taint_decide⟩

/-- `bkLoad 8` reads the stack at a public address. -/
theorem bkLoad_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs []) (.block (bkLoad 8)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem oneRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1]) (.block oneRest) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln T : BitVec 64}

/-- `OneI`, with the tag's address `T` in `s9`, which the state may write,
and the data, which it may write too. -/
def OneT (c W sp : Addr) (R : Nat) (Np : Addr) (n : Nat) (Ad A D Ln T : BitVec 64) (s : State) : Prop :=
  OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s9 = T ∧ Covers [⟨T, 16⟩] s.wr ∧ OD false c W D D Ln s

theorem OneT.frame {s s' : State} (h : OneT c W sp R Np n Ad A D Ln T s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneT c W sp R Np n Ad A D Ln T s' :=
  ⟨h.1.frame hV he hrd hwr hsp hf hs, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    by rw [hwr]; exact h.2.2.1, h.2.2.2.of_eq hrd hwr hsp⟩

/-- Between `oneAad` and `oneTag`: the additional data `a` absorbed and padded. -/
def OneAbs (c W : Addr) (A : BitVec 64) (s : State) : Prop :=
  ∃ H : Block, ∃ a : List Byte, blockAt s.mem (c + BitVec.ofNat 64 240) = H ∧ A.toNat = a.length ∧
    Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length))

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
  (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 16⟩)
include L hR hTW

/-- `seal` after its entry. -/
theorem sealBody_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : CT (fun s => OneT c W sp R Np n Ad A D Ln T s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n)
    (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.seq (.block tagOut) (.block restore))))) := by
  -- `oneAad`
  refine CT.seq (J := fun s => OneT c W sp R Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) (A := Ad) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, i]; exact hA) (by rw [d]; exact sa))) fun s' ⟨oa, rd, wr, sp'⟩ =>
        ⟨hT.frame (fun r hr => (he.fr r hr).symm) oa.env rd wr sp' oa.frame
          (fun hd' => by rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'),
        blockAt s.mem (V .s2 + BitVec.ofNat 64 240), bytesAt s.mem Ad (V .s10).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneCrypt`
  refine CT.seq (J := fun s => OneT c W sp R Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneCrypt_ct L hR (o := false) (Dst := D)).mono fun s ⟨hT, _⟩ => ⟨hT.1, hT.2.2.2, Bool.noConfusion⟩)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have L' := L.v a b d
    have hd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat := by rw [a, b, d, k]; exact hT.2.2.2.1
    refine WP.mono (WP.with_rdwr (oneCrypt_ok L' he e hR hd (by rw [d]; exact sd) rfl)) fun s' ⟨oc, rd, wr, sp'⟩ =>
      ⟨hT.frame (fun r hr => (he.fr r hr).symm) oc.env rd wr sp' oc.frame
        (fun hd' => by rw [← d]; exact slot_crFrame L' hd hd'), H, x, ?_, hl, ?_⟩
    · rw [← a, blockAt_frame oc.frame (fun r hr => (ctx_crFrame L' hd r hr).sub_left (Lay.ctxSub (by decide)))]
      rw [← a] at hH; exact hH
    · have hx := Nat.mod_lt (x ++ zeros (padLen x.length)).length (show 16 > 0 by decide)
      rw [← b] at hab ⊢
      exact hab.congr (blockAt_frame oc.frame (stp_crFrame L' hd (by decide)))
        (bytesAt_frame oc.frame (stp_crFrame L' hd (by omega_using [])) (by omega_using []))
  -- `oneTag 0`
  refine CT.seq (J := fun s => ∃ V : Reg → BitVec 64, V .s0 = W ∧ V .s9 = T ∧ Env V sp s ∧
    Covers [⟨T, 16⟩] s.wr) ((oneTag_ct L (.inl rfl) hR).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneTag_ok (L.v a b d) (o := 0) (.inl rfl) (H := H) (a := x) (D := D) he e hR
      (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab) (by rw [b, d, k]; exact hD)
      (by rw [d]; exact sd)))
      fun s' ⟨ot, _, wr, _⟩ => ⟨V, d, (he.fr _ (by decide)).symm.trans hT.2.1, ot.env, by rw [wr]; exact hT.2.2.1⟩
  -- the tag copied out
  refine CT.seq (J := fun s => s.gpr .s0 = W ∧ s.sp = sp) ?_
    (fun s ⟨V, d, i, he, hT⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT) (by rw [i, d]; exact hTW))
      fun s' ⟨_, _, hg, hk⟩ => ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, d₁, i₁, h₁, _⟩ ⟨_, d₂, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => W) sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end

theorem seal_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa sealRISCV64.pre sealRISCV64.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩ := hq
  have h₁' : sealPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, fW, _, hR, _, ca, wa⟩ := h₁'
  let I₀ : State → Prop := fun s => sealPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm,
    q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm, (qa 1 (by decide)).symm⟩, ?_⟩
  refine CT.seq (J := fun s => OneT (σ₁.gpr .a0) (stackArg σ₁ 1) σ₁.sp (σ₁.gpr .a1).toNat (σ₁.gpr .a2)
    (σ₁.gpr .a3).toNat (σ₁.gpr .a4) (σ₁.gpr .a5) (σ₁.gpr .a6) (σ₁.gpr .a7) (stackArg σ₁ 0) s ∧
    s.gpr .s4 = σ₁.gpr .a2 ∧ s.gpr .s5 = BitVec.ofNat 64 (σ₁.gpr .a3).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1⟩ => ?_)
    (sealBody_ct (oneLay fc fW dcW ca wa) hR (dtW.sub_right (Region.sub_prefix (by decide))))
  · -- the entry: its head loads `W` from a public address, the rest saves through it
    let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 1 else σ₁.gpr r
    rw [oneEntry_eq]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := oneHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, ea1⟩
      have hA : Covers [args s 2] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      have hsa : s.sp.toNat % 16 = 0 := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := hs
        exact hk.1
      refine WP.mono (oneA_ok (W := stackArg s 1) (.inl rfl) hsa (args_in hA (by decide) (i := 1) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea1, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := oneRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  · have := sealEntry_wp hs
    rw [ea0, ea1, e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
    exact WP.mono this fun s' ⟨hO, h24, h25, h20, hT, hOD⟩ => ⟨⟨hO, h20, hT, hOD⟩, h24, h25⟩

end VG.Proof.AesGcm.RISCV64
