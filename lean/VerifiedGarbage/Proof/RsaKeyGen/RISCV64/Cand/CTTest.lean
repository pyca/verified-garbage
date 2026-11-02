module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTTop
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTTop
import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on RISC-V: the test in constant time

`test_ct`: two runs of the test (trial division, then Miller–Rabin and the
result), from calls with the same public data and stack pointer, leak the
same trace, as on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/CTTest.lean`):
trial division by its own constant time (`DivOk.ct`), from candidates its
table divides alike (`tt_divRel`); whether it found a divisor, and the test's
result, are the same in both runs (`comp_agree`, `shape_eq`). The loads
from the frame (`out`'s address and length in `finPrime`) are cut after, as
in `CTTop.lean`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Mont (off word)
open VG.Proof.MillerRabin.RISCV64 (Env RoundImpl)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (test testResult testArgs finish finNone finPrime ldf stf oOut oOutLen
  oRead seqs)

/-! ## What two runs share once `gcd(c − 1, e) = 1` -/

/-- The candidate is not too close to `p`, and `gcd(c − 1, e) = 1`. -/
structure TtG (s0 : State) : Prop where
  ncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false
  gcd : Nat.gcd (candOf s0 - 1) (eV s0) = 1

theorem tt_candS {s0 : State} (hp : CIn s0) (hav : oL s0 ≤ rL s0) : candS s0 = candOf s0 := candS_eq hp hav

theorem tt_comp_agree {a : KD} {s0 s0' : State} (k : KR a s0) (k' : KR a s0') (g : TtG s0)
    (hav : oL s0 ≤ rL s0) :
    Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) =
      Spec.RsaKeyGen.obviouslyComposite (64 * cw s0') (candOf s0') := by
  have hav' : oL s0' ≤ rL s0' := by rw [← k.1.oL_eq k'.1, ← k.1.rL_eq k'.1]; exact hav
  obtain ⟨hw, -, -⟩ := cw_facts k.1.1
  obtain ⟨hw', -, -⟩ := cw_facts k'.1.1
  have e := comp_agree k.1 k'.1 hav
    (by rw [tt_candS k.1.1 hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact g.ncl)
  rwa [tt_candS k.1.1 hav, tt_candS k'.1.1 hav', hw, hw', show 8 * (8 * cw s0) = 64 * cw s0 by omega,
    show 8 * (8 * cw s0') = 64 * cw s0' by omega] at e

theorem tt_comp_same {a : KD} {s0 s0' : State} (k : KR a s0) (k' : KR a s0') (g : TtG s0)
    (hav : oL s0 ≤ rL s0) (ho : Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) = true) :
    candOf s0 = candOf s0' := by
  have hav' : oL s0' ≤ rL s0' := by rw [← k.1.oL_eq k'.1, ← k.1.rL_eq k'.1]; exact hav
  obtain ⟨hw, -, -⟩ := cw_facts k.1.1
  have e := comp_same k.1 k'.1 hav
    (by rw [tt_candS k.1.1 hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact g.ncl)
    (by rw [tt_candS k.1.1 hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact ho)
  rwa [tt_candS k.1.1 hav, tt_candS k'.1.1 hav'] at e

/-! ## The stages -/

/-- After the test's arguments. -/
def TtA (s0 s : State) : Prop := T1 s0 (cw s0) (candOf s0) s ∧ TtG s0

/-- After trial division. -/
def TtB (s0 s : State) : Prop := T2 s0 (cw s0) (candOf s0) s ∧ TtG s0

/-- The registers `Env` and the frame fix. -/
def ttEnvOf (s0 : State) (r : Reg) : BitVec 64 :=
  if r = .s11 then fb s0 else if r = .s6 then stackArg s0 1
  else if r = .t0 then BitVec.ofNat 64 (cw s0) else if r = .a7 then off (stackArg s0 1) (slot (cw s0) 0)
  else BitVec.ofNat 64 (8 * (cw s0 + 2))

theorem tt_envOf_agree (rs : List Reg) :
    ∀ (a : KD) (x y : State), KR a x → KR a y → ∀ r ∈ rs, ttEnvOf x r = ttEnvOf y r := by
  intro a x y kx ky r _
  unfold ttEnvOf
  rw [kx.fb ky, kx.arg ky (i := 1) (by decide), kx.cw ky]

theorem tt_envOf_env {s0 t : State} {Z : Nat} (e : Env t (stackArg s0 1) Z (cw s0)) (hf : Fr s0 t) :
    ∀ r ∈ ([.s11, .s6, .t0, .a7, .s5] : List Reg), t.gpr r = ttEnvOf s0 r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hf.s11
  · exact e.s6
  · exact e.t0
  · exact e.a7
  · exact e.s5

theorem tt_pins_env {X : State → State → Prop} {rs : List Reg}
    (hrs : ∀ r ∈ rs, r ∈ ([.s11, .s6, .t0, .a7, .s5] : List Reg))
    (hx : ∀ s0 t, X s0 t → ∃ Z, Env t (stackArg s0 1) Z (cw s0) ∧ Fr s0 t) : Pins (SG X) rs :=
  pins_of ttEnvOf (tt_envOf_agree rs) fun s0 t h r hr => by
    obtain ⟨Z, e, hf⟩ := hx s0 t h
    exact tt_envOf_env e hf r (hrs r hr)

/-! ## Trial division -/

theorem tt_c8 {s0 : State} (hp : CIn s0) : 8161 < candOf s0 := by
  obtain ⟨-, hw4, -⟩ := cw_facts hp
  have := (VG.Proof.RsaKeyGen.candidate_shape (bits := 64 * cw s0) (by omega)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a7) (8 * cw s0)))).2.1
  have : 2 ^ 14 ≤ 2 ^ (64 * cw s0 - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  show 8161 < Spec.RsaKeyGen.candidate (64 * cw s0) _
  omega

/-- Candidates the table divides alike. -/
theorem tt_divRel {a : KD} {s₁ s₂ : State} (h₁ : SG TtA a s₁) (h₂ : SG TtA a s₂) (hsp : s₁.sp = s₂.sp) :
    DivRel s₁ s₂ := by
  obtain ⟨s0, k, t1, g⟩ := h₁
  obtain ⟨s0', k', t1', g'⟩ := h₂
  have d := t1.divIn
  have d' := t1'.divIn
  have hB : stackArg s0 1 = stackArg s0' 1 := k.arg k' (i := 1) (by decide)
  have hL : sL s0 = sL s0' := by simp only [sL, k.arg k' (i := 2) (by decide)]
  have hw : cw s0 = cw s0' := k.cw k'
  rw [hB, hL, hw] at d
  have a0 := t1.arr0
  rw [hB, hw] at a0
  refine ⟨stackArg s0' 1, 8 * sL s0', cw s0', nTrial (cw s0'), d, d', hsp,
    by rw [t1.syms, t1'.syms]; exact k.1.sym k'.1, fun i hi => ?_⟩
  rw [a0, t1'.arr0]
  have hav : oL s0 ≤ rL s0 := by rw [t1.tc.hw]; exact t1.tc.h8
  have none : ∀ {t : State}, CIn t → Spec.RsaKeyGen.obviouslyComposite (64 * cw t) (candOf t) = false →
      ∀ j < nTrial (cw t), VG.Proof.RsaKeyGen.entryDivides (candOf t) j = false := by
    intro t ht hc j hj
    have hp := VG.Proof.RsaKeyGen.trialPrefix_spec (w := cw t) (tt_c8 ht)
    rw [hc] at hp
    cases he : VG.Proof.RsaKeyGen.entryDivides (candOf t) j
    · rfl
    · rw [show nTrial (cw t) = if cw t ≤ 16 then 512 else 1024 from rfl] at hj
      rw [VG.Proof.RsaKeyGen.trialPrefix_hit hj he] at hp; cases hp
  cases ho : Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0)
  · have ho' := (tt_comp_agree k k' g hav).symm.trans ho
    rw [none k.1.1 ho i (by rw [hw]; exact hi), none k'.1.1 ho' i hi]
  · rw [tt_comp_same k k' g hav ho]

/-! ## The end of a run keeps the stack pointer -/

theorem tt_sp {α : Type} {Φ : α → State → Prop} {c : Prog isa}
    (h : RelCT isa (Two Φ) c fun _ _ => True) : RelCT isa (Two Φ) c fun t₁ t₂ => t₁.sp = t₂.sp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨_, -, -, hsp⟩ := hp
  exact ⟨ht, show s₁'.sp = s₂'.sp by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]⟩

/-! ## The result -/

/-- What two runs share after the witnesses: the prepared candidate's state,
not too close to `p`, and `gcd(c − 1, e) = 1`. -/
def TtR (s0 : State) : Prop := (∃ q, T3 s0 (cw s0) (candOf s0) q) ∧ TtG s0

theorem TtR.lctx {a : KD} {s0 : State} (k : KR a s0) (h : TtR s0) : ∃ q, LCtx a.1 s0 q := by
  obtain ⟨⟨q, t3⟩, g⟩ := h
  exact ⟨q, ⟨k.1, t3, g.ncl, g.gcd⟩⟩

/-- The test's status, from what became of the candidate. -/
def ttSt (s0 : State) : Nat :=
  match Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0)) with
  | none => 0
  | some (b, _) => if b then 1 else 2

theorem ttSt_shape (s0 : State) : ttSt s0 = (VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0)
    ((rB s0).drop (8 * cw s0)))).elim 0 fun x => if x.1 then 1 else 2 := by
  unfold ttSt VG.Proof.RsaKeyGen.shapeOf
  rcases Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0)) with _ | ⟨b, rest⟩ <;> rfl

theorem ttSt_eq {a : KD} {s0 s0' : State} (k : KR a s0) (k' : KR a s0') (h : TtR s0) (h' : TtR s0') :
    ttSt s0 = ttSt s0' := by
  obtain ⟨q, C⟩ := h.lctx k
  obtain ⟨q', C'⟩ := h'.lctx k'
  rw [ttSt_shape, ttSt_shape, shape_eq C C']

theorem ttSt_lt (s0 : State) : ttSt s0 < 3 := by
  unfold ttSt
  split
  · decide
  · split <;> decide

/-- After the witnesses. -/
def TtD (s0 s : State) : Prop := TtR s0 ∧ T4 s0 (cw s0) (candOf s0) s

/-- After the status is loaded (`r` its value less `k`). -/
def TtS (k : Nat) (s0 t : State) : Prop :=
  TtR s0 ∧ Ctx s0 t ∧ Env t (stackArg s0 1) (8 * sL s0) (cw s0) ∧
    t.gpr .t2 = BitVec.ofNat 64 (ttSt s0) - BitVec.ofNat 64 k

theorem TtS.envFr {k : Nat} {s0 t : State} (h : TtS k s0 t) : ∃ Z, Env t (stackArg s0 1) Z (cw s0) ∧ Fr s0 t :=
  ⟨_, h.2.2.1, h.2.1.fr⟩

theorem TtD.envFr {s0 t : State} (h : TtD s0 t) : ∃ Z, Env t (stackArg s0 1) Z (cw s0) ∧ Fr s0 t :=
  ⟨_, h.2.prep.env, h.2.ctx.fr⟩

theorem T4.ttStat {s0 s : State} (h : T4 s0 (cw s0) (candOf s0) s) :
    word s.mem (stackArg s0 1) (8 * VG.Impl.MillerRabin.RISCV64.Search.hStat) = BitVec.ofNat 64 (ttSt s0) := by
  have r := h.res
  unfold ttSt
  revert r
  rcases Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0)) with _ | ⟨b, rest⟩
  · exact id
  · exact fun r => r.1

/-- `testResult`'s first block: the octets read, and the status in `t2`. -/
theorem tt_res1_ok {s0 u : State} (h : TtD s0 u) :
    WP isa (.block [VG.Impl.MillerRabin.RISCV64.Search.ldh .t2 VG.Impl.MillerRabin.RISCV64.Search.hUsed,
      stf .t2 oRead, VG.Impl.MillerRabin.RISCV64.Search.ldh .t2 VG.Impl.MillerRabin.RISCV64.Search.hStat]) u
      (TtS 0 s0) := by
  have hc := h.2.ctx
  have hf := hc.fr
  have hP := hf.pre
  have e := h.2.prep.env
  have hst := h.2.ttStat
  generalize hB : stackArg s0 1 = B at e hst
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (cw s0 + 2)) ≤ 8 * sL s0 := e.hZ
  have keepS : ∀ (m : Mem) (v : BitVec 64) (d : Nat), d + 8 ≤ 8 * sL s0 →
      (m.writeW (fw s0 oRead) v).readW (off B d) 64 = m.readW (off B d) 64 :=
    fun m v d hd =>
      ((Frame.refl [rdW s0] m).writeW (r := rdW s0) (List.mem_singleton_self _) v (Region.contains_self _ _)).readW
        (r := ⟨off B d, 8⟩) (Region.contains_self _ _) (fun ρ hρ => by
          simp only [List.mem_singleton] at hρ; subst hρ
          refine (hP.FS.sub_left (fw_sub s0 (o := oRead) (n := 8) (by decide))).symm.sub_left ?_
          rw [← hB]
          exact Offset.sub_base (stackArg s0 1) (d := d) (n := 8) (k := (stackArg s0 2).toNat * 8)
            (by simp only [sL] at hd; omega_arith)) (by decide)
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hP h8
  have hW : InRegions u.wr (fb s0 + BitVec.ofNat 64 176) 8 :=
    ⟨kF s0, by rw [hf.wr]; exact List.mem_cons_self, kF_contains (by decide)⟩
  have r160 : (u.mem.writeW (fb s0 + 176#64) (u.mem.readW (B + 152#64) 64)).readW (B + 160#64) 64 =
      u.mem.readW (B + 160#64) 64 := keepS _ _ 160 (by omega_arith)
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun t =>
      t.mem = u.mem.writeW (fw s0 oRead) (word u.mem B (8 * VG.Impl.MillerRabin.RISCV64.Search.hUsed)) ∧
        t.gpr .t2 = word u.mem B (8 * VG.Impl.MillerRabin.RISCV64.Search.hStat)) (by
    simp only [VG.Impl.MillerRabin.RISCV64.Search.ldh, VG.Impl.MillerRabin.RISCV64.Search.hUsed,
      VG.Impl.MillerRabin.RISCV64.Search.hStat, stf, oRead]
    brun [e.s6, hf.s11, hs.ld (d := 152) (n := 8) (by omega_arith), hs.al8 (d := 152) (by omega_arith) (by decide),
      hs.ld (d := 160) (n := 8) (by omega_arith), hs.al8 (d := 160) (by omega_arith) (by decide),
      al 176 (by decide), hW, r160]) (by rfl) (by rfl))) fun t₁ ⟨⟨⟨m₁, a₁⟩, k₁⟩, rd₁, wr₁, sp₁⟩ => ?_
  have c₁ : Ctx s0 t₁ := hc.step sp₁ k₁.2.1 k₁.2.2 (k₁.gpr (by decide)) (by
    rw [m₁]
    exact (Frame.refl _ _).writeW (r := rdW s0) (w := 64) (by simp) _ (Region.contains_self _ _))
  refine ⟨h.1, c₁, ?_, ?_⟩
  · rw [hB]; exact e.keep k₁ (by decide)
  · rw [a₁, hst, BitVec.sub_zero]

/-- The status less one. -/
theorem tt_res2_ok {s0 t : State} (h : TtS 0 s0 t) : WP isa (.block [.addi .t2 .t2 (-1)]) t (TtS 1 s0) := by
  obtain ⟨r, c, e, h2⟩ := h
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun t' => t'.gpr .t2 = BitVec.ofNat 64 (ttSt s0) - BitVec.ofNat 64 1 ∧
      t'.mem = t.mem) (by
    brun [h2]
    rw [BitVec.sub_zero]) (by rfl) (by rfl))) fun t' ⟨⟨⟨a, m⟩, k⟩, _, _, sp⟩ => ?_
  exact ⟨r, c.step sp k.2.1 k.2.2 (k.gpr (by decide)) (by rw [m]; exact Frame.refl _ _), e.keep k (by decide), a⟩

/-- `finPrime`'s first block: the addresses of the copy, and its count. -/
theorem tt_copyA_ok {s0 s : State} (h : TtS 1 s0 s) :
    WP isa (.block [ldf .t5 oOutLen, .add .t3 .a7 .t5, .addi .t3 .t3 (-1), ldf .t4 oOut]) s fun t =>
      t.gpr .t3 = off (stackArg s0 1) (256 + oL s0 - 1) ∧ t.gpr .t4 = off (s0.gpr .a0) 0 ∧
        t.gpr .t5 = BitVec.ofNat 64 (oL s0) := by
  obtain ⟨-, c, e, -⟩ := h
  have hf := c.fr
  have hp := hf.pre
  have hL1 : 32 ≤ oL s0 := hp.valid.1
  have hL2 : oL s0 ≤ 512 := oL_le hp
  have eL : s0.gpr .a1 = BitVec.ofNat 64 (oL s0) := by rw [oL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [hf.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have r104 : s.mem.readW (fb s0 + BitVec.ofNat 64 104) 64 = s0.gpr .a0 := hf.wOut
  have r112 : s.mem.readW (fb s0 + BitVec.ofNat 64 112) 64 = BitVec.ofNat 64 (oL s0) := eL ▸ hf.wOutLen
  have e0 : slot (cw s0) 0 = 256 := by simp [slot, VG.Impl.Bignum.hdrBytes]
  have h7 : s.gpr .a7 = off (stackArg s0 1) 256 := by rw [e.a7, e0]
  brun [ldf, oOut, oOutLen, hf.s11, al 104 (by decide), al 112 (by decide), inr 104 (by decide),
    inr 112 (by decide), r104, r112, h7, add_ofNat_zero]
  exact VG.Proof.Rsa.RISCV64.Keys.keys_sub1 _ (by omega_arith)

/-- `finPrime`'s copy keeps the frame. -/
theorem tt_copy_fr {s0 s : State} (h : TtS 1 s0 s) :
    WP isa (.seq (.block [ldf .t5 oOutLen, .add .t3 .a7 .t5, .addi .t3 .t3 (-1), ldf .t4 oOut])
      (VG.Impl.Bignum.RISCV64.countLoop .t5
        [.load .b .t2 .t3 0, .store .b .t2 .t4 0, .addi .t4 .t4 1, .addi .t3 .t3 (-1)])) s (Fr s0) := by
  obtain ⟨-, c, e, -⟩ := h
  have hp := c.fr.pre
  have e0 : slot (cw s0) 0 = 256 := by simp [slot, VG.Impl.Bignum.hdrBytes]
  have h7 : s.gpr .a7 = off (stackArg s0 1) 256 := by rw [e.a7, e0]
  have hcS : (cO s0).Disjoint ⟨stackArg s0 1, 8 * sL s0⟩ := by
    have := hp.oS; simp only [cS, sL] at this ⊢; rwa [Nat.mul_comm]
  obtain ⟨hw, -, -⟩ := cw_facts hp
  have hZ : 256 + 28 * (8 * (cw s0 + 2)) ≤ 8 * sL s0 := e.hZ
  have cp := copyOut_ok c.fr e.hs h7 rfl rfl (by omega) hcS
  refine WP.mono (WP.rdwr cp) fun t ⟨⟨_, ho, k⟩, _, _, sp⟩ => ?_
  have fo : Frame [cO s0] s.mem t.mem := fun x hx => ho x (Or.inr (by
    have := hx _ List.mem_cons_self
    simp only [Region.Contains, VG.Proof.Mont.ofs, oL] at this ⊢
    omega_arith))
  exact c.fr.step sp k.2.1 k.2.2 (k.1 _ (by decide)) (fo.mono (by simp))

/-! ## Composing -/

/-- `(a; b); c` as `a; (b; c)`. -/
theorem tt_assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ e₁ =>
    cases e₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq a₂ e₂ =>
        cases e₂ with
        | seq b₂ c₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ b₁) c₁) (.seq (.seq a₂ b₂) c₂)
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

/-- The copy's registers: a function of the call's public data. -/
def ttCopyOf (s0 : State) (r : Reg) : BitVec 64 :=
  if r = .t3 then off (stackArg s0 1) (256 + oL s0 - 1) else if r = .t4 then off (s0.gpr .a0) 0
  else BitVec.ofNat 64 (oL s0)

theorem tt_finPrime_ct {X X' : State → State → Prop} (hx : ∀ s0 t, X s0 t → TtS 1 s0 t)
    (hw : ∀ s0 t, X s0 t → WP isa finPrime t (X' s0)) :
    RelCT isa (Two (SG X)) finPrime fun _ _ => True := by
  unfold finPrime
  refine tt_assoc (cutW (Y := fun s0 t => Fr s0 t) (X' := X') (fun s0 t h => tt_copy_fr (hx s0 t h))
    (fun s0 t h => by
      have w := hw s0 t h
      unfold finPrime at w
      exact WP.seq_iff.mpr (WP.seq_iff.mpr (WP.mono (WP.seq_iff.mp w) fun _ h => WP.seq_iff.mp h))) ?_
    (wk (fun _ _ _ _ h => h.1) (finish_rel 1 (by decide))))
  refine cutW (X' := fun _ _ => True) (fun s0 t h => tt_copyA_ok (hx s0 t h))
    (fun s0 t h => WP.mono (tt_copy_fr (hx s0 t h)) fun _ _ => trivial)
    (two_taint _ (pins_fr fun s0 t h => (hx s0 t h).2.1.fr) (by taint_decide)) ?_
  refine two_taint [.t3, .t4, .t5] (pins_of ttCopyOf ?_ fun s0 t ⟨⟨h3, h4, h5⟩, _⟩ r hr => ?_) (by taint_decide)
  · intro a x y kx ky r _
    unfold ttCopyOf
    rw [kx.arg ky (i := 1) (by decide), kx.reg ky (r := .a0) (by decide), kx.1.oL_eq ky.1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [ttCopyOf, h3, h4, h5]

/-- `testResult`: the status, and the end it chooses. -/
theorem tt_result_ct : RelCT isa (Two (SG TtD)) testResult fun _ _ => True := by
  unfold testResult
  refine cutW (Y := TtS 0) (X' := fun s0 t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem) (fun _ _ h => tt_res1_ok h)
    (fun _ _ h => h.2.result_ok)
    (two_taint _ (tt_pins_env (rs := [.s6, .s11]) (by decide) fun _ _ h => h.envFr) (by taint_decide)) ?_
  refine iteK ?_ (wk (fun _ _ _ _ h => h.1.1.2.1.fr) finNone_rel) ?_
  · rintro a s₁ s₂ ⟨s0, k, r, -, -, h2⟩ ⟨s0', k', r', -, -, h2'⟩
    rw [Steps.eval_zero, Steps.eval_zero, h2, h2', ttSt_eq k k' r r']
  refine cutW (Y := TtS 1) (X' := fun s0 t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem)
    (fun _ _ h => tt_res2_ok h.1.1) (fun _ _ h => h.2) (two_taint [] pins_nil (by taint_decide)) ?_
  refine iteK ?_ (tt_finPrime_ct (fun _ _ h => h.1.1) fun _ _ h => h.2)
    (wk (fun _ _ _ _ h => h.1.1.2.1.fr) (finish_rel 3 (by decide)))
  · rintro a s₁ s₂ ⟨s0, k, r, -, -, h2⟩ ⟨s0', k', r', -, -, h2'⟩
    rw [Steps.eval_zero, Steps.eval_zero, h2, h2', ttSt_eq k k' r r']

/-- After montPrepHi. -/
def TtP (s0 s : State) : Prop := T3 s0 (cw s0) (candOf s0) s ∧ TtG s0

theorem tt_mr_ct (R : RoundImpl) :
    RelCT isa (Two (SG TtP)) (VG.Impl.RsaKeyGen.RISCV64.Witness.millerRabin R.name R.code) fun _ _ => True :=
  (mr_ct R).mono (fun s₁ _ ⟨a, ⟨s0, k, t3, g⟩, ⟨s0', k', t3', g'⟩, hsp⟩ =>
    ⟨(a.1, s₁.sp), ⟨s0, ⟨k.1, t3, g.ncl, g.gcd⟩, rfl⟩, ⟨s0', ⟨k'.1, t3', g'.ncl, g'.gcd⟩, hsp.symm⟩⟩)
    fun _ _ _ => trivial

/-- The test, once `gcd(c − 1, e) = 1`: two runs leak the same, and keep the
stack pointer. -/
theorem test_ct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    RelCT isa (Two TSt) (test trial R.name R.code) fun t₁ t₂ => t₁.sp = t₂.sp := by
  refine tt_sp ?_
  show RelCT isa (Two (SG fun s0 s => M4 s0 s ∧ Nat.gcd (candOf s0 - 1) (eV s0) = 1)) _ _
  unfold test
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := SG TtA) (two_taint _ (tt_pins_env (rs := [.s11, .s6, .t0]) (by decide)
      fun _ _ h => ⟨_, h.1.env, h.1.ctx.fr⟩) (by taint_decide))
    fun a s ⟨s0, k, m4, g⟩ => WP.mono (argsS (toTIn m4 g)) fun t ht => ⟨s0, k, ht, ⟨m4.ncl, g⟩⟩) ?_
  refine RelCT.seq (two_post (Ψ := SG TtB) (D.ct fun s₁ s₂ ⟨a, h₁, h₂, hsp⟩ => tt_divRel h₁ h₂ hsp)
    fun a s ⟨s0, k, t1, g⟩ => WP.mono (trialS D t1) fun t ht => ⟨s0, k, ht, g⟩) ?_
  refine iteW ?_ (wk (fun _ _ _ _ h => h.1.1.ctx.fr) (finish_rel 3 (by decide))) ?_
  · rintro a s₁ s₂ ⟨s0, k, t2, g⟩ ⟨s0', k', t2', g'⟩
    rw [Steps.eval_nonzero_ofNat _ _ (by split <;> decide) t2.f,
      Steps.eval_nonzero_ofNat _ _ (by split <;> decide) t2'.f,
      tt_comp_agree k k' g (by rw [t2.tc.hw]; exact t2.tc.h8)]
  refine RelCT.seq (two_post (Ψ := SG TtP) (two_taint _ (tt_pins_env (rs := [.a7, .s5, .t0, .s6]) (by decide)
      fun _ _ h => ⟨_, h.1.1.env, h.1.1.ctx.fr⟩) (by taint_decide))
    fun a s ⟨s0, k, ⟨t2, g⟩, ev⟩ => ?_) ?_
  · have hoc : Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) = false := by
      rw [Steps.eval_nonzero_ofNat _ _ (by split <;> decide) t2.f] at ev
      revert ev; cases Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) <;> decide
    exact WP.mono (prepS t2 hoc) fun t ht => ⟨s0, k, ht, g⟩
  exact RelCT.seq (two_post (Ψ := SG TtD) (tt_mr_ct R) fun a s ⟨s0, k, t3, g⟩ =>
    WP.mono (mrStage R t3) fun t ht => ⟨s0, k, ⟨⟨s, t3⟩, g⟩, ht⟩) tt_result_ct

end VG.Proof.RsaKeyGen.RISCV64.Cand
